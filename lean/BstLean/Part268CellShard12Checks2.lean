import BstLean.Part268CellShard12Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12650_40 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (41348114990377 / 50000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257810116707 / 100000000000000 : ℝ))
      (E := (cell12650 ⟨40, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (41348114990377 / 50000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257810116707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_41 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (826622104941 / 1000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257814099243 / 100000000000000 : ℝ))
      (E := (cell12650 ⟨41, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (826622104941 / 1000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257814099243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_42 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (20657053660277 / 25000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257818116223 / 100000000000000 : ℝ))
      (E := (cell12650 ⟨42, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (20657053660277 / 25000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257818116223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_43 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (5162140149503 / 6250000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257822108141 / 100000000000000 : ℝ))
      (E := (cell12650 ⟨43, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (5162140149503 / 6250000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257822108141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_44 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (82560293717341 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (564456533213 / 25000000000000 : ℝ))
      (E := (cell12650 ⟨44, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (82560293717341 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (564456533213 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_45 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (20631592146889 / 25000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (564457532591 / 25000000000000 : ℝ))
      (E := (cell12650 ⟨45, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (20631592146889 / 25000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (564457532591 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_46 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (20623116743353 / 25000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (1128917049631 / 50000000000000 : ℝ))
      (E := (cell12650 ⟨46, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (20623116743353 / 25000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (1128917049631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_47 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (20614647211443 / 25000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (112891904841 / 5000000000000 : ℝ))
      (E := (cell12650 ⟨47, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (20614647211443 / 25000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (112891904841 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_48 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (82424734175649 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (112892106063 / 5000000000000 : ℝ))
      (E := (cell12650 ⟨48, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (82424734175649 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (112892106063 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_49 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (411954514671 / 500000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257846111637 / 100000000000000 : ℝ))
      (E := (cell12650 ⟨49, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (411954514671 / 500000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257846111637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_50 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (3294283803709 / 4000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (451570024931 / 20000000000000 : ℝ))
      (E := (cell12650 ⟨50, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (3294283803709 / 4000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (451570024931 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_51 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (5145206913917 / 6250000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257854157893 / 100000000000000 : ℝ))
      (E := (cell12650 ⟨51, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (5145206913917 / 6250000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257854157893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_52 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (82289549495629 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257858149699 / 100000000000000 : ℝ))
      (E := (cell12650 ⟨52, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (82289549495629 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257858149699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_53 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (3290232467333 / 4000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (564465539053 / 25000000000000 : ℝ))
      (E := (cell12650 ⟨53, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (3290232467333 / 4000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (564465539053 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_54 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (16444419431527 / 20000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (1128933087189 / 50000000000000 : ℝ))
      (E := (cell12650 ⟨54, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (16444419431527 / 20000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (1128933087189 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_55 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (8218840589057 / 10000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (564467535461 / 25000000000000 : ℝ))
      (E := (cell12650 ⟨55, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (8218840589057 / 10000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (564467535461 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_56 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (82154737854283 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257874173307 / 100000000000000 : ℝ))
      (E := (cell12650 ⟨56, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (82154737854283 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257874173307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_57 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (41060546510533 / 50000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (564469536719 / 25000000000000 : ℝ))
      (E := (cell12650 ⟨57, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (41060546510533 / 50000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (564469536719 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_58 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (82087471363349 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257882176927 / 100000000000000 : ℝ))
      (E := (cell12650 ⟨58, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (82087471363349 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257882176927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_59 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (41026936426849 / 50000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257886200253 / 100000000000000 : ℝ))
      (E := (cell12650 ⟨59, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (41026936426849 / 50000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257886200253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12651_40 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (82696227266867 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257685582751 / 100000000000000 : ℝ))
      (E := (cell12651 ⟨40, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (82696227266867 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257685582751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_41 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (16532441616943 / 20000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (1128844808033 / 50000000000000 : ℝ))
      (E := (cell12651 ⟨41, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (16532441616943 / 20000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (1128844808033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_42 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (82628212535803 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (1128846812891 / 50000000000000 : ℝ))
      (E := (cell12651 ⟨42, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (82628212535803 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (1128846812891 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_43 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (20648560147601 / 25000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257697611131 / 100000000000000 : ℝ))
      (E := (cell12651 ⟨43, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (20648560147601 / 25000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257697611131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_44 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (82560292218939 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257701629967 / 100000000000000 : ℝ))
      (E := (cell12651 ⟨44, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (82560292218939 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257701629967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_45 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (82526367391979 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (1128852811149 / 50000000000000 : ℝ))
      (E := (cell12651 ⟨45, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (82526367391979 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (1128852811149 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_46 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (82492466080241 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257709645593 / 100000000000000 : ℝ))
      (E := (cell12651 ⟨46, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (82492466080241 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257709645593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_47 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (644207720739 / 781250000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (112885681969 / 5000000000000 : ℝ))
      (E := (cell12651 ⟨47, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (644207720739 / 781250000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (112885681969 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_48 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (82424733886043 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257717601811 / 100000000000000 : ℝ))
      (E := (cell12651 ⟨48, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (82424733886043 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257717601811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_49 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (82390902945753 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257721648731 / 100000000000000 : ℝ))
      (E := (cell12651 ⟨49, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (82390902945753 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257721648731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_50 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (2573659231407 / 3125000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257725660051 / 100000000000000 : ℝ))
      (E := (cell12651 ⟨50, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (2573659231407 / 3125000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257725660051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_51 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (41161655617651 / 50000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (1128864816641 / 50000000000000 : ℝ))
      (E := (cell12651 ⟨51, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (41161655617651 / 50000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (1128864816641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_52 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (82289550408177 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (564433406187 / 25000000000000 : ℝ))
      (E := (cell12651 ⟨52, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (82289550408177 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (564433406187 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_53 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (4112790644769 / 5000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257737631607 / 100000000000000 : ℝ))
      (E := (cell12651 ⟨53, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (4112790644769 / 5000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257737631607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_54 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (5138881166799 / 6250000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257741650809 / 100000000000000 : ℝ))
      (E := (cell12651 ⟨54, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (5138881166799 / 6250000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257741650809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_55 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (82188407700403 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257745679093 / 100000000000000 : ℝ))
      (E := (cell12651 ⟨55, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (82188407700403 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257745679093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_56 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (8215473996239 / 10000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (225774965387 / 10000000000000 : ℝ))
      (E := (cell12651 ⟨56, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (8215473996239 / 10000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (225774965387 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_57 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (41060547713519 / 50000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (564438422419 / 25000000000000 : ℝ))
      (E := (cell12651 ⟨57, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (41060547713519 / 50000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (564438422419 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_58 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (10260934258347 / 12500000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257757664367 / 100000000000000 : ℝ))
      (E := (cell12651 ⟨58, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (10260934258347 / 12500000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257757664367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_59 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (82053875854173 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257761692157 / 100000000000000 : ℝ))
      (E := (cell12651 ⟨59, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (82053875854173 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257761692157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12652_40 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (82696224553867 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257561104319 / 100000000000000 : ℝ))
      (E := (cell12652 ⟨40, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (82696224553867 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257561104319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_41 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (41331102838089 / 50000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (141097820607 / 6250000000000 : ℝ))
      (E := (cell12652 ⟨41, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (41331102838089 / 50000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (141097820607 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_42 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (8262821043131 / 10000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (11287845661 / 500000000000 : ℝ))
      (E := (cell12652 ⟨42, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (8262821043131 / 10000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (11287845661 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_43 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (16518847757907 / 20000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257573169831 / 100000000000000 : ℝ))
      (E := (cell12652 ⟨43, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (16518847757907 / 20000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257573169831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_44 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (3302411628851 / 4000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257577124017 / 100000000000000 : ℝ))
      (E := (cell12652 ⟨44, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (3302411628851 / 4000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257577124017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_45 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (41263183098551 / 50000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (1128790585033 / 50000000000000 : ℝ))
      (E := (cell12652 ⟨45, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (41263183098551 / 50000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (1128790585033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_46 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (41246232593867 / 50000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257585130051 / 100000000000000 : ℝ))
      (E := (cell12652 ⟨46, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (41246232593867 / 50000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257585130051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_47 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (41229293832019 / 50000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257589178989 / 100000000000000 : ℝ))
      (E := (cell12652 ⟨47, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (41229293832019 / 50000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257589178989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_48 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (20606183399257 / 25000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257593138377 / 100000000000000 : ℝ))
      (E := (cell12652 ⟨48, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (20606183399257 / 25000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257593138377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_49 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (4119545147893 / 5000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257597182949 / 100000000000000 : ℝ))
      (E := (cell12652 ⟨49, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (4119545147893 / 5000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257597182949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_50 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (1029463696473 / 1250000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257601192609 / 100000000000000 : ℝ))
      (E := (cell12652 ⟨50, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (1029463696473 / 1250000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257601192609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_51 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (82323311848413 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (225760516487 / 10000000000000 : ℝ))
      (E := (cell12652 ⟨51, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (82323311848413 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (225760516487 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_52 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (82289551321169 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (282201144507 / 12500000000000 : ℝ))
      (E := (cell12652 ⟨52, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (82289551321169 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (282201144507 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_53 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (41127907053921 / 50000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (564403290831 / 25000000000000 : ℝ))
      (E := (cell12652 ⟨53, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (41127907053921 / 50000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (564403290831 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_54 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (16444420036061 / 20000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (1128808591811 / 50000000000000 : ℝ))
      (E := (cell12652 ⟨54, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (16444420036061 / 20000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (1128808591811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_55 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (20547102377643 / 25000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257621213689 / 100000000000000 : ℝ))
      (E := (cell12652 ⟨55, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (20547102377643 / 25000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257621213689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_56 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (20538685517699 / 25000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257625190937 / 100000000000000 : ℝ))
      (E := (cell12652 ⟨56, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (20538685517699 / 25000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257625190937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_57 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (10265137229159 / 12500000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257629229899 / 100000000000000 : ℝ))
      (E := (cell12652 ⟨57, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (10265137229159 / 12500000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257629229899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_58 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (8208747677043 / 10000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (225763320843 / 10000000000000 : ℝ))
      (E := (cell12652 ⟨58, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (8208747677043 / 10000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (225763320843 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_59 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (82053878854839 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (1128818620373 / 50000000000000 : ℝ))
      (E := (cell12652 ⟨59, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (82053878854839 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (1128818620373 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12653_40 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (82696221841751 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257436681413 / 100000000000000 : ℝ))
      (E := (cell12653 ⟨40, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (82696221841751 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257436681413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_41 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (82662203268489 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (35272510921 / 1562500000000 : ℝ))
      (E := (cell12653 ⟨41, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (82662203268489 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (35272510921 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_42 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (82628208327627 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257444694267 / 100000000000000 : ℝ))
      (E := (cell12653 ⟨42, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (82628208327627 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257444694267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_43 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (1008230432 / 1220703125 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (1128724362713 / 50000000000000 : ℝ))
      (E := (cell12653 ⟨43, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (1008230432 / 1220703125 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (1128724362713 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_44 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (20640072306087 / 25000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (1128726366337 / 50000000000000 : ℝ))
      (E := (cell12653 ⟨44, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (20640072306087 / 25000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (1128726366337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_45 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (3301054600117 / 4000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (451491342961 / 20000000000000 : ℝ))
      (E := (cell12653 ⟨45, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (3301054600117 / 4000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (451491342961 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_46 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (82492464295891 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (451492145857 / 20000000000000 : ℝ))
      (E := (cell12653 ⟨46, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (82492464295891 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (451492145857 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_47 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (1288415423033 / 1562500000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257464715643 / 100000000000000 : ℝ))
      (E := (cell12653 ⟨47, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (1288415423033 / 1562500000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257464715643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_48 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (41212366654301 / 50000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (28218359137 / 1250000000000 : ℝ))
      (E := (cell12653 ⟨48, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (41212366654301 / 50000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (28218359137 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_49 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (82390902970521 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (141092044643 / 6250000000000 : ℝ))
      (E := (cell12653 ⟨49, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (82390902970521 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (141092044643 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_50 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (20589274007793 / 25000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257476722327 / 100000000000000 : ℝ))
      (E := (cell12653 ⟨50, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (20589274007793 / 25000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257476722327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_51 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (20580828115501 / 25000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257480752657 / 100000000000000 : ℝ))
      (E := (cell12653 ⟨51, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (20580828115501 / 25000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257480752657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_52 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (41144776117303 / 50000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257484743623 / 100000000000000 : ℝ))
      (E := (cell12653 ⟨52, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (41144776117303 / 50000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257484743623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_53 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (10281976915089 / 12500000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (1763663087 / 78125000000 : ℝ))
      (E := (cell12653 ⟨53, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (10281976915089 / 12500000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (1763663087 / 78125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_54 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (82222101692197 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (451498554563 / 20000000000000 : ℝ))
      (E := (cell12653 ⟨54, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (82222101692197 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (451498554563 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_55 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (3287536452843 / 4000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257496745631 / 100000000000000 : ℝ))
      (E := (cell12653 ⟨55, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (3287536452843 / 4000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257496745631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_56 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (82154744179501 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (282187598063 / 12500000000000 : ℝ))
      (E := (cell12653 ⟨56, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (82154744179501 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (282187598063 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_57 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (82121100239769 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257504767541 / 100000000000000 : ℝ))
      (E := (cell12653 ⟨57, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (82121100239769 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257504767541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_58 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (82087479474311 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (451501761823 / 20000000000000 : ℝ))
      (E := (cell12653 ⟨58, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (82087479474311 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (451501761823 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_59 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (5128367615981 / 6250000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257512786827 / 100000000000000 : ℝ))
      (E := (cell12653 ⟨59, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (5128367615981 / 6250000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257512786827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12654_40 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (2067405478263 / 2500000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (564328078509 / 25000000000000 : ℝ))
      (E := (cell12654 ⟨40, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (2067405478263 / 2500000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (564328078509 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_41 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (5166387553853 / 6250000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (1128658161883 / 50000000000000 : ℝ))
      (E := (cell12654 ⟨41, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (5166387553853 / 6250000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (1128658161883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_42 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (20657051556189 / 25000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (141082519499 / 6250000000000 : ℝ))
      (E := (cell12654 ⟨42, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (20657051556189 / 25000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (141082519499 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_43 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (41297117595059 / 50000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (451464867347 / 20000000000000 : ℝ))
      (E := (cell12654 ⟨43, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (41297117595059 / 50000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (451464867347 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_44 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (82560287728159 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257328338267 / 100000000000000 : ℝ))
      (E := (cell12654 ⟨44, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (82560287728159 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257328338267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_45 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (82526363809449 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257332315379 / 100000000000000 : ℝ))
      (E := (cell12654 ⟨45, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (82526363809449 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257332315379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_46 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (82492463404711 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (564334081383 / 25000000000000 : ℝ))
      (E := (cell12654 ⟨46, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (82492463404711 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (564334081383 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_47 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (82458586484813 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (1128670183581 / 50000000000000 : ℝ))
      (E := (cell12654 ⟨47, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (82458586484813 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (1128670183581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_48 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (82424733020767 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (225734432063 / 10000000000000 : ℝ))
      (E := (cell12654 ⟨48, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (82424733020767 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (225734432063 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_49 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (10298862872967 / 12500000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (112867418033 / 5000000000000 : ℝ))
      (E := (cell12654 ⟨49, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (10298862872967 / 12500000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (112867418033 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_50 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (41178548172511 / 50000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (1128676183581 / 50000000000000 : ℝ))
      (E := (cell12654 ⟨50, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (41178548172511 / 50000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (1128676183581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_51 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (3292932523043 / 4000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257356337643 / 100000000000000 : ℝ))
      (E := (cell12654 ⟨51, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (3292932523043 / 4000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257356337643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_52 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (82289553148487 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (564340096863 / 25000000000000 : ℝ))
      (E := (cell12654 ⟨52, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (82289553148487 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (564340096863 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_53 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (8225581653399 / 10000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257364395719 / 100000000000000 : ℝ))
      (E := (cell12654 ⟨53, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (8225581653399 / 10000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257364395719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_54 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (82222103204461 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257368359319 / 100000000000000 : ℝ))
      (E := (cell12654 ⟨54, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (82222103204461 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257368359319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_55 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (41094206565957 / 50000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (282171549139 / 12500000000000 : ℝ))
      (E := (cell12654 ⟨55, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (41094206565957 / 50000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (282171549139 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_56 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (16430949257701 / 20000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257376375457 / 100000000000000 : ℝ))
      (E := (cell12654 ⟨56, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (16430949257701 / 20000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257376375457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_57 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (82121102646529 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257380361747 / 100000000000000 : ℝ))
      (E := (cell12654 ⟨57, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (82121102646529 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257380361747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_58 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (41043741089209 / 50000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257384407261 / 100000000000000 : ℝ))
      (E := (cell12654 ⟨58, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (41043741089209 / 50000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257384407261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_59 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (82053884856743 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (564347097399 / 25000000000000 : ℝ))
      (E := (cell12654 ⟨59, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (82053884856743 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (564347097399 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12655_40 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (41348108210087 / 50000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257187943443 / 100000000000000 : ℝ))
      (E := (cell12655 ⟨40, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (41348108210087 / 50000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257187943443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_41 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (41331099227827 / 50000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257191945411 / 100000000000000 : ℝ))
      (E := (cell12655 ⟨41, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (41331099227827 / 50000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257191945411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_42 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (16525640824539 / 20000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (282149498169 / 12500000000000 : ℝ))
      (E := (cell12655 ⟨42, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (16525640824539 / 20000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (282149498169 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_43 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (82594233391571 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (451440000751 / 20000000000000 : ℝ))
      (E := (cell12655 ⟨43, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (82594233391571 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (451440000751 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_44 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (41280143116353 / 50000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (451440799927 / 20000000000000 : ℝ))
      (E := (cell12655 ⟨44, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (41280143116353 / 50000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (451440799927 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_45 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (82526362616673 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257207971787 / 100000000000000 : ℝ))
      (E := (cell12655 ⟨45, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (82526362616673 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257207971787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_46 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (16498492502839 / 20000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (1128605988837 / 50000000000000 : ℝ))
      (E := (cell12655 ⟨46, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (16498492502839 / 20000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (1128605988837 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_47 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (4122929294807 / 5000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257216015731 / 100000000000000 : ℝ))
      (E := (cell12655 ⟨47, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (4122929294807 / 5000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257216015731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_48 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (41212366366761 / 50000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257219966317 / 100000000000000 : ℝ))
      (E := (cell12655 ⟨48, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (41212366366761 / 50000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257219966317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_49 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (160919732417 / 195312500000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (564306001039 / 25000000000000 : ℝ))
      (E := (cell12655 ⟨49, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (160919732417 / 195312500000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (564306001039 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_50 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (82357096659389 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (1128614004579 / 50000000000000 : ℝ))
      (E := (cell12655 ⟨50, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (82357096659389 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (1128614004579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_51 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (82323313690627 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (225723197883 / 10000000000000 : ℝ))
      (E := (cell12655 ⟨51, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (82323313690627 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (225723197883 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_52 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (20572388515703 / 25000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257236028517 / 100000000000000 : ℝ))
      (E := (cell12655 ⟨52, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (20572388515703 / 25000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257236028517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_53 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (20563954436919 / 25000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257240037351 / 100000000000000 : ℝ))
      (E := (cell12655 ⟨53, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (20563954436919 / 25000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257240037351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_54 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (10277763089637 / 12500000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (1128622001103 / 50000000000000 : ℝ))
      (E := (cell12655 ⟨54, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (10277763089637 / 12500000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (1128622001103 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_55 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (5136775933943 / 6250000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257248037941 / 100000000000000 : ℝ))
      (E := (cell12655 ⟨55, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (5136775933943 / 6250000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257248037941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_56 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (5134671774863 / 6250000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (1128626011457 / 50000000000000 : ℝ))
      (E := (cell12655 ⟨56, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (5134671774863 / 6250000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (1128626011457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_57 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (5132569065847 / 6250000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (1128628006259 / 50000000000000 : ℝ))
      (E := (cell12655 ⟨57, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (5132569065847 / 6250000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (1128628006259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_58 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (1282616951293 / 1562500000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257260062031 / 100000000000000 : ℝ))
      (E := (cell12655 ⟨58, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (1282616951293 / 1562500000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257260062031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_59 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (4102694392899 / 5000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (45145280981 / 2000000000000 : ℝ))
      (E := (cell12655 ⟨59, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (4102694392899 / 5000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (45145280981 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12656_40 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (10337026713839 / 12500000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (112853181419 / 5000000000000 : ℝ))
      (E := (cell12656 ⟨40, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (10337026713839 / 12500000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (112853181419 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_41 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (20665549012627 / 25000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257067681413 / 100000000000000 : ℝ))
      (E := (cell12656 ⟨41, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (20665549012627 / 25000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257067681413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_42 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (20657050505361 / 25000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257071655583 / 100000000000000 : ℝ))
      (E := (cell12656 ⟨42, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (20657050505361 / 25000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257071655583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_43 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (20648557898449 / 25000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (564268916919 / 25000000000000 : ℝ))
      (E := (cell12656 ⟨43, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (20648557898449 / 25000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (564268916919 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_44 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (82560284737989 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (112853982897 / 5000000000000 : ℝ))
      (E := (cell12656 ⟨44, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (82560284737989 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (112853982897 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_45 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (82526361424597 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (225708368403 / 10000000000000 : ℝ))
      (E := (cell12656 ⟨45, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (82526361424597 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (225708368403 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_46 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (41246230812171 / 50000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257087685713 / 100000000000000 : ℝ))
      (E := (cell12656 ⟨46, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (41246230812171 / 50000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257087685713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_47 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (82458585308093 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257091661351 / 100000000000000 : ℝ))
      (E := (cell12656 ⟨47, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (82458585308093 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257091661351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_48 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (82424732446867 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257095668023 / 100000000000000 : ℝ))
      (E := (cell12656 ⟨48, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (82424732446867 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257095668023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_49 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (5149431438239 / 6250000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (1128549851867 / 50000000000000 : ℝ))
      (E := (cell12656 ⟨49, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (5149431438239 / 6250000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (1128549851867 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_50 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (1286829640223 / 1562500000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (70534490853 / 3125000000000 : ℝ))
      (E := (cell12656 ⟨50, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (1286829640223 / 1562500000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (70534490853 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_51 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (4116165715283 / 5000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257107676217 / 100000000000000 : ℝ))
      (E := (cell12656 ⟨51, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (4116165715283 / 5000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257107676217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_52 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (4114477748879 / 5000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (451422345169 / 20000000000000 : ℝ))
      (E := (cell12656 ⟨52, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (4114477748879 / 5000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (451422345169 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_53 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (10281977370221 / 12500000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (1128557838129 / 50000000000000 : ℝ))
      (E := (cell12656 ⟨53, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (10281977370221 / 12500000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (1128557838129 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_54 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (82222106230101 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (1128559850739 / 50000000000000 : ℝ))
      (E := (cell12656 ⟨54, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (82222106230101 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (1128559850739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_55 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (20547104188649 / 25000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (451424747843 / 20000000000000 : ℝ))
      (E := (cell12656 ⟨55, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (20547104188649 / 25000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (451424747843 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_56 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (82154750507409 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257127726877 / 100000000000000 : ℝ))
      (E := (cell12656 ⟨56, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (82154750507409 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257127726877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_57 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (82121107460837 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (451426343971 / 20000000000000 : ℝ))
      (E := (cell12656 ⟨57, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (82121107460837 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (451426343971 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_58 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (5130467974207 / 6250000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (1128567857131 / 50000000000000 : ℝ))
      (E := (cell12656 ⟨58, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (5130467974207 / 6250000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (1128567857131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_59 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (82053890859407 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257139706001 / 100000000000000 : ℝ))
      (E := (cell12656 ⟨59, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (82053890859407 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257139706001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12657_40 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (41348105501067 / 50000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (141058710553 / 6250000000000 : ℝ))
      (E := (cell12657 ⟨40, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (41348105501067 / 50000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (141058710553 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_41 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (82662193646209 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (1128471677737 / 50000000000000 : ℝ))
      (E := (cell12657 ⟨41, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (82662193646209 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (1128471677737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_42 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (20657049980251 / 25000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (1128473690733 / 50000000000000 : ℝ))
      (E := (cell12657 ⟨42, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (20657049980251 / 25000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (1128473690733 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_43 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (16518845959359 / 20000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256951387311 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨43, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (16518845959359 / 20000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256951387311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_44 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (82560283244009 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256955372021 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨44, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (82560283244009 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256955372021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_45 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (4126318011661 / 5000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256959393251 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨45, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (4126318011661 / 5000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256959393251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_46 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (82492460735151 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256963390767 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨46, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (82492460735151 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256963390767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_47 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (2576830772521 / 3125000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (1128483710919 / 50000000000000 : ℝ))
      (E := (cell12657 ⟨47, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (2576830772521 / 3125000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (1128483710919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_48 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (82424732160801 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (9027885703 / 400000000000 : ℝ))
      (E := (cell12657 ⟨48, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (82424732160801 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (9027885703 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_49 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (41195451513349 / 50000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (1128487700219 / 50000000000000 : ℝ))
      (E := (cell12657 ⟨49, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (41195451513349 / 50000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (1128487700219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_50 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (10294637161209 / 12500000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256979402597 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨50, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (10294637161209 / 12500000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256979402597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_51 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (20580828730293 / 25000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256983429809 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨51, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (20580828730293 / 25000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256983429809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_52 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (10286194486599 / 12500000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (564246855103 / 25000000000000 : ℝ))
      (E := (cell12657 ⟨52, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (10286194486599 / 12500000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (564246855103 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_53 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (20563955044067 / 25000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256991430539 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨53, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (20563955044067 / 25000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256991430539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_54 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (41111053871739 / 50000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (451399091427 / 20000000000000 : ℝ))
      (E := (cell12657 ⟨54, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (41111053871739 / 50000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (451399091427 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_55 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (82188418566439 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (28212492973 / 1250000000000 : ℝ))
      (E := (cell12657 ⟨55, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (82188418566439 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (28212492973 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_56 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (82154752617309 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2257003428227 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨56, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (82154752617309 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2257003428227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_57 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (2566284683387 / 3125000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2257007424617 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨57, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (2566284683387 / 3125000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2257007424617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_58 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (41043745146049 / 50000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2257011423121 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨58, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (41043745146049 / 50000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2257011423121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_59 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (3282155754441 / 4000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (225701547883 / 10000000000000 : ℝ))
      (E := (cell12657 ⟨59, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (3282155754441 / 4000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (225701547883 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12658_40 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (2067405207361 / 2500000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (282101888263 / 12500000000000 : ℝ))
      (E := (cell12658 ⟨40, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (2067405207361 / 2500000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (282101888263 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_41 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (20665547810689 / 25000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (451363828779 / 20000000000000 : ℝ))
      (E := (cell12658 ⟨41, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (20665547810689 / 25000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (451363828779 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_42 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (82628197821373 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (564205790751 / 25000000000000 : ℝ))
      (E := (cell12658 ⟨42, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (82628197821373 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (564205790751 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_43 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (82594228000567 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (1128413581331 / 50000000000000 : ℝ))
      (E := (cell12658 ⟨43, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (82594228000567 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (1128413581331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_44 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (16512056350153 / 20000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256831141879 / 100000000000000 : ℝ))
      (E := (cell12658 ⟨44, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (16512056350153 / 20000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256831141879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_45 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (82526359042543 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (225683515831 / 10000000000000 : ℝ))
      (E := (cell12658 ⟨45, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (82526359042543 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (225683515831 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_46 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (82492459846623 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (56420978793 / 2500000000000 : ℝ))
      (E := (cell12658 ⟨46, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (82492459846623 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (56420978793 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_47 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (41229292066939 / 50000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (141052698711 / 6250000000000 : ℝ))
      (E := (cell12658 ⟨47, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (41229292066939 / 50000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (141052698711 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_48 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (20606182968831 / 25000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256847180567 / 100000000000000 : ℝ))
      (E := (cell12658 ⟨48, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (20606182968831 / 25000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256847180567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_49 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (659127224337 / 800000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256851153223 / 100000000000000 : ℝ))
      (E := (cell12658 ⟨49, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (659127224337 / 800000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256851153223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_50 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (82357097605587 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256855154043 / 100000000000000 : ℝ))
      (E := (cell12658 ⟨50, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (82357097605587 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256855154043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_51 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (82323315537163 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256859180603 / 100000000000000 : ℝ))
      (E := (cell12658 ⟨51, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (82323315537163 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256859180603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_52 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (82289556808447 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256863171243 / 100000000000000 : ℝ))
      (E := (cell12658 ⟨52, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (82289556808447 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256863171243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_53 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (3290232855647 / 4000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (141054198881 / 6250000000000 : ℝ))
      (E := (cell12658 ⟨53, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (3290232855647 / 4000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (141054198881 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_54 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (3288884370289 / 4000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (1128435605053 / 50000000000000 : ℝ))
      (E := (cell12658 ⟨54, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (3288884370289 / 4000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (1128435605053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_55 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (10273552547327 / 12500000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256875192911 / 100000000000000 : ℝ))
      (E := (cell12658 ⟨55, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (10273552547327 / 12500000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256875192911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_56 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (41077377363753 / 50000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (1128439593043 / 50000000000000 : ℝ))
      (E := (cell12658 ⟨56, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (41077377363753 / 50000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (1128439593043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_57 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (82121112276193 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256883185947 / 100000000000000 : ℝ))
      (E := (cell12658 ⟨57, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (82121112276193 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256883185947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_58 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (8208749299711 / 10000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256887188607 / 100000000000000 : ℝ))
      (E := (cell12658 ⟨58, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (8208749299711 / 10000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256887188607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_59 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (5128368553927 / 6250000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256891189969 / 100000000000000 : ℝ))
      (E := (cell12658 ⟨59, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (5128368553927 / 6250000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256891189969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12659_40 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (82696205587629 / 100000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (564172724723 / 25000000000000 : ℝ))
      (E := (cell12659 ⟨40, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (82696205587629 / 100000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (564172724723 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_41 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (1653243776803 / 2000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (1128347464571 / 50000000000000 : ℝ))
      (E := (cell12659 ⟨41, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (1653243776803 / 2000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (1128347464571 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_42 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (10328524465319 / 12500000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256698941407 / 100000000000000 : ℝ))
      (E := (cell12659 ⟨42, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (10328524465319 / 12500000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256698941407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_43 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (10324278275639 / 12500000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (1128351467457 / 50000000000000 : ℝ))
      (E := (cell12659 ⟨43, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (10324278275639 / 12500000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (1128351467457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_44 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (82560280258257 / 100000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (1128353483757 / 50000000000000 : ℝ))
      (E := (cell12659 ⟨44, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (82560280258257 / 100000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (1128353483757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_45 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (20631589463141 / 25000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (1128355460173 / 50000000000000 : ℝ))
      (E := (cell12659 ⟨45, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (20631589463141 / 25000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (1128355460173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_46 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (41246229479379 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256714968571 / 100000000000000 : ℝ))
      (E := (cell12659 ⟨46, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (41246229479379 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256714968571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_47 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (82458583547709 / 100000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (141044933373 / 6250000000000 : ℝ))
      (E := (cell12659 ⟨47, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (82458583547709 / 100000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (141044933373 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_48 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (82424731590437 / 100000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256722932473 / 100000000000000 : ℝ))
      (E := (cell12659 ⟨48, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (82424731590437 / 100000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256722932473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_49 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (10298862882263 / 12500000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256726962091 / 100000000000000 : ℝ))
      (E := (cell12659 ⟨49, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (10298862882263 / 12500000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256726962091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_50 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (82357097922019 / 100000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256730961631 / 100000000000000 : ℝ))
      (E := (cell12659 ⟨50, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (82357097922019 / 100000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256730961631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_51 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (16464663230727 / 20000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (5641837469 / 250000000000 : ℝ))
      (E := (cell12659 ⟨51, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (16464663230727 / 20000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (5641837469 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_52 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (16457911544909 / 20000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (112836948917 / 5000000000000 : ℝ))
      (E := (cell12659 ⟨52, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (16457911544909 / 20000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (112836948917 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_53 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (82255822606489 / 100000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256742989979 / 100000000000000 : ℝ))
      (E := (cell12659 ⟨53, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (82255822606489 / 100000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256742989979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_54 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (82222110771343 / 100000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (225674696039 / 10000000000000 : ℝ))
      (E := (cell12659 ⟨54, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (82222110771343 / 100000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (225674696039 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_55 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (10273552773891 / 12500000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256751004429 / 100000000000000 : ℝ))
      (E := (cell12659 ⟨55, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (10273552773891 / 12500000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256751004429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_56 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (41077378419001 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256755000451 / 100000000000000 : ℝ))
      (E := (cell12659 ⟨56, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (41077378419001 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256755000451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_57 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (10265139335533 / 12500000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (451351800769 / 20000000000000 : ℝ))
      (E := (cell12659 ⟨57, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (10265139335533 / 12500000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (451351800769 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_58 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (20521873925587 / 25000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256763010723 / 100000000000000 : ℝ))
      (E := (cell12659 ⟨58, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (20521873925587 / 25000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256763010723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_59 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (8205389986483 / 10000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (451353403397 / 20000000000000 : ℝ))
      (E := (cell12659 ⟨59, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (8205389986483 / 10000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (451353403397 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12660_40 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (41348101440851 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256566747213 / 100000000000000 : ℝ))
      (E := (cell12660 ⟨40, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (41348101440851 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256566747213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_41 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (82662186438391 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (35258918281 / 1562500000000 : ℝ))
      (E := (cell12660 ⟨41, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (82662186438391 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (35258918281 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_42 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (4131409681227 / 5000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (451314955093 / 20000000000000 : ℝ))
      (E := (cell12660 ⟨42, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (4131409681227 / 5000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (451314955093 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_43 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (82594224410429 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (564144690721 / 25000000000000 : ℝ))
      (E := (cell12660 ⟨43, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (82594224410429 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (564144690721 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_44 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (16512055753297 / 20000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256582790089 / 100000000000000 : ℝ))
      (E := (cell12660 ⟨44, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (16512055753297 / 20000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256582790089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_45 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (16505271332657 / 20000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (1128293398541 / 50000000000000 : ℝ))
      (E := (cell12660 ⟨45, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (16505271332657 / 20000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (1128293398541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_46 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (41246229035777 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (56414769561 / 2500000000000 : ℝ))
      (E := (cell12660 ⟨46, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (41246229035777 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (56414769561 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_47 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (41229291481083 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256594803429 / 100000000000000 : ℝ))
      (E := (cell12660 ⟨47, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (41229291481083 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256594803429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_48 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (41212365653069 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (451319759867 / 20000000000000 : ℝ))
      (E := (cell12660 ⟨48, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (41212365653069 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (451319759867 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_49 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (16478180614927 / 20000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (282075346011 / 12500000000000 : ℝ))
      (E := (cell12660 ⟨49, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (16478180614927 / 20000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (282075346011 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_50 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (82357098238967 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (564151706341 / 25000000000000 : ℝ))
      (E := (cell12660 ⟨50, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (82357098238967 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (564151706341 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_51 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (16464663354117 / 20000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (1128305395901 / 50000000000000 : ℝ))
      (E := (cell12660 ⟨51, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (16464663354117 / 20000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (1128305395901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_52 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (82289558641087 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (564153695669 / 25000000000000 : ℝ))
      (E := (cell12660 ⟨52, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (82289558641087 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (564153695669 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_53 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (82255823822209 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (112830939757 / 5000000000000 : ℝ))
      (E := (cell12660 ⟨53, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (82255823822209 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (112830939757 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_54 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (82222112285831 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (451324565227 / 20000000000000 : ℝ))
      (E := (cell12660 ⟨54, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (82222112285831 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (451324565227 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_55 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (41094212001987 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256626813299 / 100000000000000 : ℝ))
      (E := (cell12660 ⟨55, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (41094212001987 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256626813299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_56 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (20538689737199 / 25000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (451326162441 / 20000000000000 : ℝ))
      (E := (cell12660 ⟨56, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (20538689737199 / 25000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (451326162441 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_57 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (82121117092597 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256634819169 / 100000000000000 : ℝ))
      (E := (cell12660 ⟨57, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (82121117092597 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256634819169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_58 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (20521874601953 / 25000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256638830301 / 100000000000000 : ℝ))
      (E := (cell12660 ⟨58, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (20521874601953 / 25000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256638830301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_59 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (82053902867017 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (1128321420751 / 50000000000000 : ℝ))
      (E := (cell12660 ⟨59, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (82053902867017 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (1128321420751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12661_40 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (41348100088329 / 50000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256442651069 / 100000000000000 : ℝ))
      (E := (cell12661 ⟨40, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (41348100088329 / 50000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256442651069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_41 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (82662184037477 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (282055825957 / 12500000000000 : ℝ))
      (E := (cell12661 ⟨41, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (82662184037477 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (282055825957 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_42 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (41314095763669 / 50000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256450606391 / 100000000000000 : ℝ))
      (E := (cell12661 ⟨42, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (41314095763669 / 50000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256450606391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_43 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (41297111308259 / 50000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (1128227323287 / 50000000000000 : ℝ))
      (E := (cell12661 ⟨43, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (41297111308259 / 50000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (1128227323287 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_44 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (10320034659431 / 12500000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (1128229334223 / 50000000000000 : ℝ))
      (E := (cell12661 ⟨44, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (10320034659431 / 12500000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (1128229334223 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_45 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (5157897217169 / 6250000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (5641156677 / 250000000000 : ℝ))
      (E := (cell12661 ⟨45, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (5157897217169 / 6250000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (5641156677 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_46 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (82492457185013 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256466652211 / 100000000000000 : ℝ))
      (E := (cell12661 ⟨46, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (82492457185013 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256466652211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_47 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (82458582377247 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256470669947 / 100000000000000 : ℝ))
      (E := (cell12661 ⟨47, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (82458582377247 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256470669947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_48 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (20606182755607 / 25000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (225647466329 / 10000000000000 : ℝ))
      (E := (cell12661 ⟨48, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (20606182755607 / 25000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (225647466329 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_49 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (82390903091719 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (1128239344563 / 50000000000000 : ℝ))
      (E := (cell12661 ⟨49, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (82390903091719 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (1128239344563 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_50 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (8235709855643 / 10000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (451296537253 / 20000000000000 : ℝ))
      (E := (cell12661 ⟨50, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (8235709855643 / 10000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (451296537253 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_51 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (16464663477603 / 20000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256486652211 / 100000000000000 : ℝ))
      (E := (cell12661 ⟨51, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (16464663477603 / 20000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256486652211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_52 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (82289559558071 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (564122675577 / 25000000000000 : ℝ))
      (E := (cell12661 ⟨52, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (82289559558071 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (564122675577 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_53 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (16451165007667 / 20000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256494656631 / 100000000000000 : ℝ))
      (E := (cell12661 ⟨53, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (16451165007667 / 20000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256494656631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_54 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (8222211380069 / 10000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256498689197 / 100000000000000 : ℝ))
      (E := (cell12661 ⟨54, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (8222211380069 / 10000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256498689197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_55 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (82188425817153 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (112825133931 / 5000000000000 : ℝ))
      (E := (cell12661 ⟨55, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (82188425817153 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (112825133931 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_56 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (5134672566243 / 6250000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (225650668047 / 10000000000000 : ℝ))
      (E := (cell12661 ⟨56, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (5134672566243 / 6250000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (225650668047 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_57 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (82121119501191 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (451302138213 / 20000000000000 : ℝ))
      (E := (cell12661 ⟨57, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (82121119501191 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (451302138213 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_58 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (41043750556751 / 50000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256514706511 / 100000000000000 : ℝ))
      (E := (cell12661 ⟨58, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (41043750556751 / 50000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256514706511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_59 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (41026952934697 / 50000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (282064840339 / 12500000000000 : ℝ))
      (E := (cell12661 ⟨59, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (41026952934697 / 50000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (282064840339 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12662_40 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (5168512342031 / 6250000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256318551717 / 100000000000000 : ℝ))
      (E := (cell12662 ⟨40, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (5168512342031 / 6250000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256318551717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_41 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (82662181637409 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256322559691 / 100000000000000 : ℝ))
      (E := (cell12662 ⟨41, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (82662181637409 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256322559691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_42 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (2582130919717 / 3125000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (451265310353 / 20000000000000 : ℝ))
      (E := (cell12662 ⟨42, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (2582130919717 / 3125000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (451265310353 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_43 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (82594220823379 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (35255164487 / 1562500000000 : ℝ))
      (E := (cell12662 ⟨43, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (82594220823379 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (35255164487 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_44 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (41280137892573 / 50000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (451266908749 / 20000000000000 : ℝ))
      (E := (cell12662 ⟨44, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (41280137892573 / 50000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (451266908749 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_45 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (82526354286821 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (1128169270749 / 50000000000000 : ℝ))
      (E := (cell12662 ⟨45, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (82526354286821 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (1128169270749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_46 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (82492456299133 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (564085644471 / 25000000000000 : ℝ))
      (E := (cell12662 ⟨46, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (82492456299133 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (564085644471 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_47 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (41229290896477 / 50000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256346533519 / 100000000000000 : ℝ))
      (E := (cell12662 ⟨47, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (41229290896477 / 50000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256346533519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_48 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (41212365369653 / 50000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256350583269 / 100000000000000 : ℝ))
      (E := (cell12662 ⟨48, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (41212365369653 / 50000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256350583269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_49 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (41195451554677 / 50000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256354548339 / 100000000000000 : ℝ))
      (E := (cell12662 ⟨49, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (41195451554677 / 50000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256354548339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_50 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (82357098874409 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256358544333 / 100000000000000 : ℝ))
      (E := (cell12662 ⟨50, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (82357098874409 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256358544333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_51 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (20580829501481 / 25000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256362568827 / 100000000000000 : ℝ))
      (E := (cell12662 ⟨51, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (20580829501481 / 25000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256362568827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_52 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (82289560475497 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (451273312031 / 20000000000000 : ℝ))
      (E := (cell12662 ⟨52, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (82289560475497 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (451273312031 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_53 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (20563956563717 / 25000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256370574449 / 100000000000000 : ℝ))
      (E := (cell12662 ⟨53, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (20563956563717 / 25000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256370574449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_54 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (41111057657959 / 50000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (282046826081 / 12500000000000 : ℝ))
      (E := (cell12662 ⟨54, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (41111057657959 / 50000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (282046826081 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_55 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (82188427630667 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (225637860039 / 10000000000000 : ℝ))
      (E := (cell12662 ⟨55, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (82188427630667 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (225637860039 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_56 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (82154763171277 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (1128191302623 / 50000000000000 : ℝ))
      (E := (cell12662 ⟨56, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (82154763171277 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (1128191302623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_57 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (82121121910047 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256386619531 / 100000000000000 : ℝ))
      (E := (cell12662 ⟨57, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (82121121910047 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256386619531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_58 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (10260937977427 / 12500000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256390639353 / 100000000000000 : ℝ))
      (E := (cell12662 ⟨58, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (10260937977427 / 12500000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256390639353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_59 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (2051347721799 / 2500000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256394601423 / 100000000000000 : ℝ))
      (E := (cell12662 ⟨59, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (2051347721799 / 2500000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256394601423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12663_40 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (82696194769217 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128097224579 / 50000000000000 : ℝ))
      (E := (cell12663 ⟨40, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (82696194769217 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128097224579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_41 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (82662179238187 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256198449789 / 100000000000000 : ℝ))
      (E := (cell12663 ⟨41, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (82662179238187 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256198449789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_42 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (82628187335359 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256202494007 / 100000000000000 : ℝ))
      (E := (cell12663 ⟨42, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (82628187335359 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256202494007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_43 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (82594219031013 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128103231741 / 50000000000000 : ℝ))
      (E := (cell12663 ⟨43, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (82594219031013 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128103231741 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_44 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (82560274295579 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (90248418993 / 4000000000000 : ℝ))
      (E := (cell12663 ⟨44, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (82560274295579 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (90248418993 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_45 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (82526353099637 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128107234019 / 50000000000000 : ℝ))
      (E := (cell12663 ⟨45, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (82526353099637 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128107234019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_46 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (16498491082783 / 20000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256218500577 / 100000000000000 : ℝ))
      (E := (cell12663 ⟨46, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (16498491082783 / 20000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256218500577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_47 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (41229290604643 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (564055627991 / 25000000000000 : ℝ))
      (E := (cell12663 ⟨47, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (41229290604643 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (564055627991 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_48 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (82424730456773 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256226500341 / 100000000000000 : ℝ))
      (E := (cell12663 ⟨48, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (82424730456773 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256226500341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_49 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (82390903127541 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128115261297 / 50000000000000 : ℝ))
      (E := (cell12663 ⟨49, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (82390903127541 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128115261297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_50 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (82357099192903 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (282029314691 / 12500000000000 : ℝ))
      (E := (cell12663 ⟨50, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (82357099192903 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (282029314691 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_51 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (10290414828039 / 12500000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256238541651 / 100000000000000 : ℝ))
      (E := (cell12663 ⟨51, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (10290414828039 / 12500000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256238541651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_52 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (82289561393367 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256242533297 / 100000000000000 : ℝ))
      (E := (cell12663 ⟨52, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (82289561393367 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256242533297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_53 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (1285247304247 / 1562500000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256246548597 / 100000000000000 : ℝ))
      (E := (cell12663 ⟨53, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (1285247304247 / 1562500000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256246548597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_54 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (20555529207879 / 25000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256250525417 / 100000000000000 : ℝ))
      (E := (cell12663 ⟨54, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (20555529207879 / 25000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256250525417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_55 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (41094214722257 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (451250903903 / 20000000000000 : ℝ))
      (E := (cell12663 ⟨55, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (41094214722257 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (451250903903 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_56 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (82154765282963 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128129263707 / 50000000000000 : ℝ))
      (E := (cell12663 ⟨56, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (82154765282963 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128129263707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_57 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (16424224863833 / 20000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128131272713 / 50000000000000 : ℝ))
      (E := (cell12663 ⟨57, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (16424224863833 / 20000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128131272713 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_58 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (82087506525557 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (112813328483 / 5000000000000 : ℝ))
      (E := (cell12663 ⟨58, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (82087506525557 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (112813328483 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_59 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (16410782374943 / 20000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256270536827 / 100000000000000 : ℝ))
      (E := (cell12663 ⟨59, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (16410782374943 / 20000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256270536827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12664_40 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (4134809603341 / 5000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (28200880761 / 1250000000000 : ℝ))
      (E := (cell12664 ⟨40, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (4134809603341 / 5000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (28200880761 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_41 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (8266217683981 / 10000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256074454253 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨41, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (8266217683981 / 10000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256074454253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_42 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (41314092620291 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256078433119 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨42, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (41314092620291 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256078433119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_43 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (82594217239417 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (1128041227759 / 50000000000000 : ℝ))
      (E := (cell12664 ⟨43, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (82594217239417 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (1128041227759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_44 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (82560272806747 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (282010807711 / 12500000000000 : ℝ))
      (E := (cell12664 ⟨44, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (82560272806747 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (282010807711 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_45 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (82526351913151 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256090450421 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨45, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (82526351913151 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256090450421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_46 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (41246227264679 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (1128047239587 / 50000000000000 : ℝ))
      (E := (cell12664 ⟨46, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (41246227264679 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (1128047239587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_47 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (82458580626243 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (1128049243733 / 50000000000000 : ℝ))
      (E := (cell12664 ⟨47, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (82458580626243 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (1128049243733 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_48 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (20606182543707 / 25000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256102473441 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨48, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (20606182543707 / 25000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256102473441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_49 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (2059772578657 / 2500000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256106493981 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨49, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (2059772578657 / 2500000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256106493981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_50 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (10294637438989 / 12500000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256110487893 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨50, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (10294637438989 / 12500000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256110487893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_51 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (41161659621589 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256114511683 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨51, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (41161659621589 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256114511683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_52 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (41144781155839 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (564029625921 / 25000000000000 : ℝ))
      (E := (cell12664 ⟨52, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (41144781155839 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (564029625921 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_53 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (82255828689153 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (1128061260013 / 50000000000000 : ℝ))
      (E := (cell12664 ⟨53, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (82255828689153 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (1128061260013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_54 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (20555529586871 / 25000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256126498577 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨54, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (20555529586871 / 25000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256126498577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_55 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (16437686251739 / 20000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (564032623773 / 25000000000000 : ℝ))
      (E := (cell12664 ⟨55, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (16437686251739 / 20000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (564032623773 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_56 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (20538691848737 / 25000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256134506093 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨56, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (20538691848737 / 25000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256134506093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_57 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (82121126728543 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (451227705579 / 20000000000000 : ℝ))
      (E := (cell12664 ⟨57, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (82121126728543 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (451227705579 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_58 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (41043754615961 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256142556601 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨58, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (41043754615961 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256142556601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_59 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (4102695743883 / 5000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (564036632231 / 25000000000000 : ℝ))
      (E := (cell12664 ⟨59, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (4102695743883 / 5000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (564036632231 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12665_40 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (16539237873061 / 20000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (563986617349 / 25000000000000 : ℝ))
      (E := (cell12665 ⟨40, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (16539237873061 / 20000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (563986617349 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_41 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (41331087221139 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (45119009111 / 2000000000000 : ℝ))
      (E := (cell12665 ⟨41, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (41331087221139 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (45119009111 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_42 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (82628183146613 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255954486683 / 100000000000000 : ℝ))
      (E := (cell12665 ⟨42, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (82628183146613 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255954486683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_43 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (82594215448593 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (563989625819 / 25000000000000 : ℝ))
      (E := (cell12665 ⟨43, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (82594215448593 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (563989625819 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_44 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (82560271318649 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (451192500867 / 20000000000000 : ℝ))
      (E := (cell12665 ⟨44, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (82560271318649 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (451192500867 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_45 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (41263175363681 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (45119329773 / 2000000000000 : ℝ))
      (E := (cell12665 ⟨45, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (41263175363681 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (45119329773 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_46 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (41246226822731 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255970513677 / 100000000000000 : ℝ))
      (E := (cell12665 ⟨46, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (41246226822731 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255970513677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_47 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (5153661252739 / 6250000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (281996814867 / 12500000000000 : ℝ))
      (E := (cell12665 ⟨47, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (5153661252739 / 6250000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (281996814867 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_48 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (8242472989347 / 10000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255978502569 / 100000000000000 : ℝ))
      (E := (cell12665 ⟨48, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (8242472989347 / 10000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255978502569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_49 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (8239090316557 / 10000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255982521457 / 100000000000000 : ℝ))
      (E := (cell12665 ⟨49, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (8239090316557 / 10000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255982521457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_50 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (16471419966287 / 20000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (281998314301 / 12500000000000 : ℝ))
      (E := (cell12665 ⟨50, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (16471419966287 / 20000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (281998314301 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_51 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (82323319862523 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (563997634481 / 25000000000000 : ℝ))
      (E := (cell12665 ⟨51, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (82323319862523 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (563997634481 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_52 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (2571548850951 / 3125000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (1127997265171 / 50000000000000 : ℝ))
      (E := (cell12665 ⟨52, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (2571548850951 / 3125000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (1127997265171 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_53 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (10281978738363 / 12500000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (563999636947 / 25000000000000 : ℝ))
      (E := (cell12665 ⟨53, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (10281978738363 / 12500000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (563999636947 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_54 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (41111059931911 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2256002528129 / 100000000000000 : ℝ))
      (E := (cell12665 ⟨54, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (41111059931911 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2256002528129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_55 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (82188433073209 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (1128003263561 / 50000000000000 : ℝ))
      (E := (cell12665 ⟨55, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (82188433073209 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (1128003263561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_56 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (82154769507229 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2256010541287 / 100000000000000 : ℝ))
      (E := (cell12665 ⟨56, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (82154769507229 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2256010541287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_57 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (82121129138183 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2256014566937 / 100000000000000 : ℝ))
      (E := (cell12665 ⟨57, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (82121129138183 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2256014566937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_58 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (5130469496157 / 6250000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (225601854101 / 10000000000000 : ℝ))
      (E := (cell12665 ⟨58, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (5130469496157 / 6250000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (225601854101 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_59 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (41026958940397 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (564005644429 / 25000000000000 : ℝ))
      (E := (cell12665 ⟨59, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (41026958940397 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (564005644429 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12666_40 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (2584255833271 / 3125000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (563955633363 / 25000000000000 : ℝ))
      (E := (cell12666 ⟨40, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (2584255833271 / 3125000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (563955633363 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_41 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (82662172045591 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255826512447 / 100000000000000 : ℝ))
      (E := (cell12666 ⟨41, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (82662172045591 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255826512447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_42 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (20657045263363 / 25000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255830537119 / 100000000000000 : ℝ))
      (E := (cell12666 ⟨42, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (20657045263363 / 25000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255830537119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_43 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (4129710682927 / 5000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255834547943 / 100000000000000 : ℝ))
      (E := (cell12666 ⟨43, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (4129710682927 / 5000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255834547943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_44 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (16512053966257 / 20000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255838543929 / 100000000000000 : ℝ))
      (E := (cell12666 ⟨44, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (16512053966257 / 20000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255838543929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_45 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (82526349542271 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255842523863 / 100000000000000 : ℝ))
      (E := (cell12666 ⟨45, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (82526349542271 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255842523863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_46 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (82492452762227 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (1127923272601 / 50000000000000 : ℝ))
      (E := (cell12666 ⟨46, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (82492452762227 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (1127923272601 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_47 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (82458579462029 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (451170109493 / 20000000000000 : ℝ))
      (E := (cell12666 ⟨47, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (82458579462029 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (451170109493 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_48 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (82424729612701 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (281981816099 / 12500000000000 : ℝ))
      (E := (cell12666 ⟨48, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (82424729612701 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (281981816099 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_49 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (82390903185411 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255858546067 / 100000000000000 : ℝ))
      (E := (cell12666 ⟨49, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (82390903185411 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255858546067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_50 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (41178550075737 / 50000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255862538093 / 100000000000000 : ℝ))
      (E := (cell12666 ⟨50, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (41178550075737 / 50000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255862538093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_51 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (41161660241173 / 50000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (18046932491 / 800000000000 : ℝ))
      (E := (cell12666 ⟨51, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (41161660241173 / 50000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (18046932491 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_52 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (82289564149627 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (451174110849 / 20000000000000 : ℝ))
      (E := (cell12666 ⟨52, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (82289564149627 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (451174110849 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_53 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (4112791556253 / 5000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255874572833 / 100000000000000 : ℝ))
      (E := (cell12666 ⟨53, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (4112791556253 / 5000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255874572833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_54 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (82222121380529 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (1127939277501 / 50000000000000 : ℝ))
      (E := (cell12666 ⟨54, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (82222121380529 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (1127939277501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_55 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (10273554361007 / 12500000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255882615607 / 100000000000000 : ℝ))
      (E := (cell12666 ⟨55, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (10273554361007 / 12500000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255882615607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_56 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (82154771619807 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (18047092591 / 800000000000 : ℝ))
      (E := (cell12666 ⟨56, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (82154771619807 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (18047092591 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_57 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (20530282887021 / 25000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (225589060341 / 10000000000000 : ℝ))
      (E := (cell12666 ⟨57, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (20530282887021 / 25000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (225589060341 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_58 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (5130469665333 / 6250000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255894582053 / 100000000000000 : ℝ))
      (E := (cell12666 ⟨58, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (5130469665333 / 6250000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255894582053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_59 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (82053920884117 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255898624013 / 100000000000000 : ℝ))
      (E := (cell12666 ⟨59, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (82053920884117 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255898624013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12667_40 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (2067404599123 / 2500000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (451139718861 / 20000000000000 : ℝ))
      (E := (cell12667 ⟨40, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (2067404599123 / 2500000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (451139718861 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_41 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (20665542412437 / 25000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (563925656237 / 25000000000000 : ℝ))
      (E := (cell12667 ⟨41, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (20665542412437 / 25000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (563925656237 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_42 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (82628178961099 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255706643217 / 100000000000000 : ℝ))
      (E := (cell12667 ⟨42, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (82628178961099 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255706643217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_43 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (82594211869257 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (451142129667 / 20000000000000 : ℝ))
      (E := (cell12667 ⟨43, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (82594211869257 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (451142129667 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_44 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (5160016771541 / 6250000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (563928659827 / 25000000000000 : ℝ))
      (E := (cell12667 ⟨44, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (5160016771541 / 6250000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (563928659827 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_45 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (82526348357877 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255718614923 / 100000000000000 : ℝ))
      (E := (cell12667 ⟨45, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (82526348357877 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255718614923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_46 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (20623112969913 / 25000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (451144526527 / 20000000000000 : ℝ))
      (E := (cell12667 ⟨46, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (20623112969913 / 25000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (451144526527 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_47 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (41229289440429 / 50000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255726631963 / 100000000000000 : ℝ))
      (E := (cell12667 ⟨47, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (41229289440429 / 50000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255726631963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_48 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (41212364666259 / 50000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255730669979 / 100000000000000 : ℝ))
      (E := (cell12667 ⟨48, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (41212364666259 / 50000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255730669979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_49 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (82390903205803 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (140983414173 / 6250000000000 : ℝ))
      (E := (cell12667 ⟨49, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (82390903205803 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (140983414173 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_50 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (82357100472027 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255738676909 / 100000000000000 : ℝ))
      (E := (cell12667 ⟨50, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (82357100472027 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255738676909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_51 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (82323321102647 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255742641037 / 100000000000000 : ℝ))
      (E := (cell12667 ⟨51, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (82323321102647 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255742641037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_52 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (16457913013853 / 20000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255746634421 / 100000000000000 : ℝ))
      (E := (cell12667 ⟨52, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (16457913013853 / 20000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255746634421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_53 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (41127916171811 / 50000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255750654211 / 100000000000000 : ℝ))
      (E := (cell12667 ⟨53, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (41127916171811 / 50000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255750654211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_54 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (16444424579521 / 20000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (1127877348671 / 50000000000000 : ℝ))
      (E := (cell12667 ⟨54, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (16444424579521 / 20000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (1127877348671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_55 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (82188436703237 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (281969837681 / 12500000000000 : ℝ))
      (E := (cell12667 ⟨55, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (82188436703237 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (281969837681 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_56 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (41077386866341 / 50000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (1127881331489 / 50000000000000 : ℝ))
      (E := (cell12667 ⟨56, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (41077386866341 / 50000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (1127881331489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_57 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (41060566979123 / 50000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255766696459 / 100000000000000 : ℝ))
      (E := (cell12667 ⟨57, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (41060566979123 / 50000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255766696459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_58 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (5130469834523 / 6250000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (563942669933 / 25000000000000 : ℝ))
      (E := (cell12667 ⟨58, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (5130469834523 / 6250000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (563942669933 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_59 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (20513480971907 / 25000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (70492960219 / 3125000000000 : ℝ))
      (E := (cell12667 ⟨59, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (20513480971907 / 25000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (70492960219 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12668_40 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (1653923625321 / 2000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255574710699 / 100000000000000 : ℝ))
      (E := (cell12668 ⟨40, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (1653923625321 / 2000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255574710699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_41 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (330648669019 / 400000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255578734283 / 100000000000000 : ℝ))
      (E := (cell12668 ⟨41, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (330648669019 / 400000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255578734283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_42 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (82628176869553 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255582746189 / 100000000000000 : ℝ))
      (E := (cell12668 ⟨42, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (82628176869553 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255582746189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_43 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (16518842016149 / 20000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127793372819 / 50000000000000 : ℝ))
      (E := (cell12668 ⟨43, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (16518842016149 / 20000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127793372819 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_44 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (2064006671469 / 2500000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (563897682909 / 25000000000000 : ℝ))
      (E := (cell12668 ⟨44, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (2064006671469 / 2500000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (563897682909 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_45 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (82526347174181 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (225559476183 / 10000000000000 : ℝ))
      (E := (cell12668 ⟨45, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (82526347174181 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (225559476183 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_46 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (41246225498869 / 50000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255598775977 / 100000000000000 : ℝ))
      (E := (cell12668 ⟨46, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (41246225498869 / 50000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255598775977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_47 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (82458578300311 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255602772431 / 100000000000000 : ℝ))
      (E := (cell12668 ⟨47, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (82458578300311 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255602772431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_48 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (82424729052923 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (563901687333 / 25000000000000 : ℝ))
      (E := (cell12668 ⟨48, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (82424729052923 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (563901687333 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_49 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (41195451613373 / 50000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (56390269089 / 2500000000000 : ℝ))
      (E := (cell12668 ⟨49, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (41195451613373 / 50000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (56390269089 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_50 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (41178550396547 / 50000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (3524398053 / 156250000000 : ℝ))
      (E := (cell12668 ⟨50, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (41178550396547 / 50000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (3524398053 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_51 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (41161660861713 / 50000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127809388457 / 50000000000000 : ℝ))
      (E := (cell12668 ⟨51, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (41161660861713 / 50000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127809388457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_52 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (82289565989343 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255622770873 / 100000000000000 : ℝ))
      (E := (cell12668 ⟨52, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (82289565989343 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255622770873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_53 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (8225583356259 / 10000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (563906697981 / 25000000000000 : ℝ))
      (E := (cell12668 ⟨53, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (8225583356259 / 10000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (563906697981 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_54 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (1644442488301 / 2000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (563907694483 / 25000000000000 : ℝ))
      (E := (cell12668 ⟨54, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (1644442488301 / 2000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (563907694483 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_55 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (13150150163 / 16000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (45112695693 / 2000000000000 : ℝ))
      (E := (cell12668 ⟨55, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (13150150163 / 16000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (45112695693 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_56 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (41077387922927 / 50000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127819404299 / 50000000000000 : ℝ))
      (E := (cell12668 ⟨56, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (41077387922927 / 50000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127819404299 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_57 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (20530284092167 / 25000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255642786941 / 100000000000000 : ℝ))
      (E := (cell12668 ⟨57, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (20530284092167 / 25000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255642786941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_58 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (82087520059633 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (45112936681 / 2000000000000 : ℝ))
      (E := (cell12668 ⟨58, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (82087520059633 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (45112936681 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_59 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (1282092607677 / 1562500000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255650827509 / 100000000000000 : ℝ))
      (E := (cell12668 ⟨59, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (1282092607677 / 1562500000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255650827509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12669_40 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (4134808928403 / 5000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (563862720659 / 25000000000000 : ℝ))
      (E := (cell12669 ⟨40, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (4134808928403 / 5000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (563862720659 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_41 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (16532432972119 / 20000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (1127727449611 / 50000000000000 : ℝ))
      (E := (cell12669 ⟨41, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (16532432972119 / 20000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (1127727449611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_42 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (16525634955763 / 20000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (281932363103 / 12500000000000 : ℝ))
      (E := (cell12669 ⟨42, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (16525634955763 / 20000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (281932363103 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_43 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (20648552073251 / 25000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (1127731449333 / 50000000000000 : ℝ))
      (E := (cell12669 ⟨43, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (20648552073251 / 25000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (1127731449333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_44 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (41280132686799 / 50000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (563866734647 / 25000000000000 : ℝ))
      (E := (cell12669 ⟨44, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (41280132686799 / 50000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (563866734647 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_45 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (82526345991181 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255470905723 / 100000000000000 : ℝ))
      (E := (cell12669 ⟨45, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (82526345991181 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255470905723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_46 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (20623112529121 / 25000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255474916343 / 100000000000000 : ℝ))
      (E := (cell12669 ⟨46, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (20623112529121 / 25000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255474916343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_47 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (82458577720387 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (56386972749 / 2500000000000 : ℝ))
      (E := (cell12669 ⟨47, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (82458577720387 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (56386972749 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_48 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (16484945754783 / 20000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (70483841989 / 3125000000000 : ℝ))
      (E := (cell12669 ⟨48, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (16484945754783 / 20000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (70483841989 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_49 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (1029886290603 / 1250000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (563871739111 / 25000000000000 : ℝ))
      (E := (cell12669 ⟨49, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (1029886290603 / 1250000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (563871739111 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_50 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (20589275278669 / 25000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (1127745473031 / 50000000000000 : ℝ))
      (E := (cell12669 ⟨50, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (20589275278669 / 25000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (1127745473031 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_51 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (82323322344683 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255494969003 / 100000000000000 : ℝ))
      (E := (cell12669 ⟨51, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (82323322344683 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255494969003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_52 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (10286195863733 / 12500000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255498963597 / 100000000000000 : ℝ))
      (E := (cell12669 ⟨52, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (10286195863733 / 12500000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255498963597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_53 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (41127917390981 / 50000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (1127751463461 / 50000000000000 : ℝ))
      (E := (cell12669 ⟨53, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (41127917390981 / 50000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (1127751463461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_54 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (1284720717701 / 1562500000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (225550697399 / 10000000000000 : ℝ))
      (E := (cell12669 ⟨54, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (1284720717701 / 1562500000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (225550697399 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_55 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (20547110083649 / 25000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (563877745851 / 25000000000000 : ℝ))
      (E := (cell12669 ⟨55, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (20547110083649 / 25000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (563877745851 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_56 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (82154777959323 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255514951613 / 100000000000000 : ℝ))
      (E := (cell12669 ⟨56, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (82154777959323 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255514951613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_57 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (82121138779351 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (451103798629 / 20000000000000 : ℝ))
      (E := (cell12669 ⟨57, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (82121138779351 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (451103798629 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_58 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (41043761383561 / 50000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255522985837 / 100000000000000 : ℝ))
      (E := (cell12669 ⟨58, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (41043761383561 / 50000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255522985837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_59 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (82053929895217 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255526984707 / 100000000000000 : ℝ))
      (E := (cell12669 ⟨59, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (82053929895217 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255526984707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12670_40 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (82696175870951 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (563831777529 / 25000000000000 : ℝ))
      (E := (cell12670 ⟨40, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (82696175870951 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (563831777529 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_41 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (20665540616821 / 25000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (1127665559883 / 50000000000000 : ℝ))
      (E := (cell12670 ⟨41, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (20665540616821 / 25000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (1127665559883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_42 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (82628172688883 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255335119127 / 100000000000000 : ℝ))
      (E := (cell12670 ⟨42, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (82628172688883 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255335119127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_43 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (5162137906627 / 6250000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255339107423 / 100000000000000 : ℝ))
      (E := (cell12670 ⟨43, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (5162137906627 / 6250000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255339107423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_44 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (82560263889169 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255343083653 / 100000000000000 : ℝ))
      (E := (cell12670 ⟨44, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (82560263889169 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255343083653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_45 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (41263172404439 / 50000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255347105467 / 100000000000000 : ℝ))
      (E := (cell12670 ⟨45, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (41263172404439 / 50000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255347105467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_46 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (8249244923589 / 10000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255351112619 / 100000000000000 : ℝ))
      (E := (cell12670 ⟨46, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (8249244923589 / 10000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255351112619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_47 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (82458577141087 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255355103461 / 100000000000000 : ℝ))
      (E := (cell12670 ⟨47, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (82458577141087 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255355103461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_48 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (41212364247747 / 50000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (281919891883 / 12500000000000 : ℝ))
      (E := (cell12670 ⟨48, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (41212364247747 / 50000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (281919891883 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_49 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (20597725817571 / 25000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (1127681573233 / 50000000000000 : ℝ))
      (E := (cell12670 ⟨49, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (20597725817571 / 25000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (1127681573233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_50 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (82357101436771 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (112768356769 / 5000000000000 : ℝ))
      (E := (cell12670 ⟨50, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (82357101436771 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (112768356769 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_51 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (41161661483209 / 50000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (451074231661 / 20000000000000 : ℝ))
      (E := (cell12670 ⟨51, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (41161661483209 / 50000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (451074231661 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_52 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (3291582713233 / 4000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (563843788393 / 25000000000000 : ℝ))
      (E := (cell12670 ⟨52, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (3291582713233 / 4000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (563843788393 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_53 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (4112791800087 / 5000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255379177307 / 100000000000000 : ℝ))
      (E := (cell12670 ⟨53, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (4112791800087 / 5000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255379177307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_54 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (82222127451047 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (563845791843 / 25000000000000 : ℝ))
      (E := (cell12670 ⟨54, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (82222127451047 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (563845791843 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_55 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (41094221075387 / 50000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (881010617 / 39062500000 : ℝ))
      (E := (cell12670 ⟨55, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (41094221075387 / 50000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (881010617 / 39062500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_56 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (641834219321 / 781250000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (563847787787 / 25000000000000 : ℝ))
      (E := (cell12670 ⟨56, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (641834219321 / 781250000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (563847787787 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_57 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (41060570595147 / 50000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255395196783 / 100000000000000 : ℝ))
      (E := (cell12670 ⟨57, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (41060570595147 / 50000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255395196783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_58 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (20521881368709 / 25000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255399194263 / 100000000000000 : ℝ))
      (E := (cell12670 ⟨58, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (20521881368709 / 25000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255399194263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_59 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (16410786579859 / 20000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (451080639721 / 20000000000000 : ℝ))
      (E := (cell12670 ⟨59, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (16410786579859 / 20000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (451080639721 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12671_40 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (41348086587361 / 50000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255203334397 / 100000000000000 : ℝ))
      (E := (cell12671 ⟨40, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (41348086587361 / 50000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255203334397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_41 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (82662160074817 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255207337147 / 100000000000000 : ℝ))
      (E := (cell12671 ⟨41, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (82662160074817 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255207337147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_42 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (82628170599757 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127605665153 / 50000000000000 : ℝ))
      (E := (cell12671 ⟨42, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (82628170599757 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127605665153 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_43 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (82594204719831 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255215313091 / 100000000000000 : ℝ))
      (E := (cell12671 ⟨43, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (82594204719831 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255215313091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_44 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (82560262405473 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127609671673 / 50000000000000 : ℝ))
      (E := (cell12671 ⟨44, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (82560262405473 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127609671673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_45 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (82526343627271 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255223361061 / 100000000000000 : ℝ))
      (E := (cell12671 ⟨45, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (82526343627271 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255223361061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_46 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (20623112088989 / 25000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127613682403 / 50000000000000 : ℝ))
      (E := (cell12671 ⟨46, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (20623112088989 / 25000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127613682403 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_47 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (8245857656241 / 10000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127615676467 / 50000000000000 : ℝ))
      (E := (cell12671 ⟨47, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (8245857656241 / 10000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127615676467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_48 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (4121236410883 / 5000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255235382513 / 100000000000000 : ℝ))
      (E := (cell12671 ⟨48, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (4121236410883 / 5000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255235382513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_49 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (41195451646439 / 50000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127619666813 / 50000000000000 : ℝ))
      (E := (cell12671 ⟨49, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (41195451646439 / 50000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127619666813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_50 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (82357101759381 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (563810845213 / 25000000000000 : ℝ))
      (E := (cell12671 ⟨50, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (82357101759381 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (563810845213 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_51 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (82323323588629 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255247344819 / 100000000000000 : ℝ))
      (E := (cell12671 ⟨51, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (82323323588629 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255247344819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_52 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (20572392188057 / 25000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127625699911 / 50000000000000 : ℝ))
      (E := (cell12671 ⟨52, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (20572392188057 / 25000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127625699911 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_53 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (41127918610961 / 50000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (281906920741 / 12500000000000 : ℝ))
      (E := (cell12671 ⟨53, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (41127918610961 / 50000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (281906920741 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_54 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (41111064484799 / 50000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127629679039 / 50000000000000 : ℝ))
      (E := (cell12671 ⟨54, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (41111064484799 / 50000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127629679039 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_55 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (16437688793457 / 20000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (563815843249 / 25000000000000 : ℝ))
      (E := (cell12671 ⟨55, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (16437688793457 / 20000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (563815843249 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_56 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (1643095643743 / 2000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2819084259 / 125000000000 : ℝ))
      (E := (cell12671 ⟨56, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (1643095643743 / 2000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2819084259 / 125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_57 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (41060571800749 / 50000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (451054279571 / 20000000000000 : ℝ))
      (E := (cell12671 ⟨57, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (41060571800749 / 50000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (451054279571 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_58 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (3283501127311 / 4000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (14095471251 / 625000000000 : ℝ))
      (E := (cell12671 ⟨58, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (3283501127311 / 4000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (14095471251 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_59 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (82053935903561 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (225527941001 / 10000000000000 : ℝ))
      (E := (cell12671 ⟨59, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (82053935903561 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (225527941001 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12672_40 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (41348085239687 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (1127539807111 / 50000000000000 : ℝ))
      (E := (cell12672 ⟨40, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (41348085239687 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (1127539807111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_41 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (82662157683193 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (281885451267 / 12500000000000 : ℝ))
      (E := (cell12672 ⟨41, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (82662157683193 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (281885451267 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_42 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (41314084255719 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (70471487411 / 3125000000000 : ℝ))
      (E := (cell12672 ⟨42, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (41314084255719 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (70471487411 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_43 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (82594202934399 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (451018326661 / 20000000000000 : ℝ))
      (E := (cell12672 ⟨43, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (82594202934399 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (451018326661 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_44 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (8256026092251 / 10000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2255095599991 / 100000000000000 : ℝ))
      (E := (cell12672 ⟨44, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (8256026092251 / 10000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2255095599991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_45 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (2063158561159 / 2500000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (451019922729 / 20000000000000 : ℝ))
      (E := (cell12672 ⟨45, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (2063158561159 / 2500000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (451019922729 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_46 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (82492447476681 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (1127551807011 / 50000000000000 : ℝ))
      (E := (cell12672 ⟨46, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (82492447476681 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (1127551807011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_47 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (20614643996089 / 25000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2255107599471 / 100000000000000 : ℝ))
      (E := (cell12672 ⟨47, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (20614643996089 / 25000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2255107599471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_48 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (20606181985103 / 25000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (281888953383 / 12500000000000 : ℝ))
      (E := (cell12672 ⟨48, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (20606181985103 / 25000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (281888953383 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_49 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (41195451658011 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (1127557817919 / 50000000000000 : ℝ))
      (E := (cell12672 ⟨49, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (41195451658011 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (1127557817919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_50 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (82357102082503 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2255119623501 / 100000000000000 : ℝ))
      (E := (cell12672 ⟨50, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (82357102082503 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2255119623501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_51 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (41161662105659 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (1127561823277 / 50000000000000 : ℝ))
      (E := (cell12672 ⟨51, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (41161662105659 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (1127561823277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_52 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (82289569674071 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (90205105733 / 4000000000000 : ℝ))
      (E := (cell12672 ⟨52, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (82289569674071 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (90205105733 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_53 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (82255838442509 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (1127565834969 / 50000000000000 : ℝ))
      (E := (cell12672 ⟨53, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (82255838442509 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (1127565834969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_54 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (41111065244259 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (17618247377 / 781250000000 : ℝ))
      (E := (cell12672 ⟨54, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (41111065244259 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (17618247377 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_55 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (82188445784129 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (563784920507 / 25000000000000 : ℝ))
      (E := (cell12672 ⟨55, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (82188445784129 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (563784920507 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_56 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (82154784301507 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (563785915163 / 25000000000000 : ℝ))
      (E := (cell12672 ⟨56, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (82154784301507 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (563785915163 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_57 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (41060573006481 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (563786913877 / 25000000000000 : ℝ))
      (E := (cell12672 ⟨57, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (41060573006481 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (563786913877 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_58 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (82087530890937 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (1127575831349 / 50000000000000 : ℝ))
      (E := (cell12672 ⟨58, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (82087530890937 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (1127575831349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_59 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (16410787781603 / 20000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (1127577839059 / 50000000000000 : ℝ))
      (E := (cell12672 ⟨59, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (16410787781603 / 20000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (1127577839059 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12673_40 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (16539233556981 / 20000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (563738972713 / 25000000000000 : ℝ))
      (E := (cell12673 ⟨40, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (16539233556981 / 20000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (563738972713 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_41 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (20665538823103 / 25000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (450991975993 / 20000000000000 : ℝ))
      (E := (cell12673 ⟨41, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (20665538823103 / 25000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (450991975993 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_42 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (41314083211963 / 50000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (563740979917 / 25000000000000 : ℝ))
      (E := (cell12673 ⟨42, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (41314083211963 / 50000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (563740979917 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_43 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (10324275143717 / 12500000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (112748394581 / 5000000000000 : ℝ))
      (E := (cell12673 ⟨43, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (10324275143717 / 12500000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (112748394581 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_44 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (2064006486007 / 2500000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254971912427 / 100000000000000 : ℝ))
      (E := (cell12673 ⟨44, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (2064006486007 / 2500000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254971912427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_45 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (16505268253229 / 20000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (1127487961041 / 50000000000000 : ℝ))
      (E := (cell12673 ⟨45, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (16505268253229 / 20000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (1127487961041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_46 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (41246223299033 / 50000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254979919151 / 100000000000000 : ℝ))
      (E := (cell12673 ⟨46, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (41246223299033 / 50000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254979919151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_47 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (3298343016277 / 4000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (70468246937 / 3125000000000 : ℝ))
      (E := (cell12673 ⟨47, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (3298343016277 / 4000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (70468246937 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_48 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (65939782131 / 80000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (563746981913 / 25000000000000 : ℝ))
      (E := (cell12673 ⟨48, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (65939782131 / 80000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (563746981913 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_49 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (16478180667943 / 20000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254991935191 / 100000000000000 : ℝ))
      (E := (cell12673 ⟨49, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (16478180667943 / 20000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254991935191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_50 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (82357102406139 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (563748980577 / 25000000000000 : ℝ))
      (E := (cell12673 ⟨50, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (82357102406139 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (563748980577 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_51 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (20580831208621 / 25000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (70468748297 / 3125000000000 : ℝ))
      (E := (cell12673 ⟨51, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (20580831208621 / 25000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (70468748297 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_52 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (20572392649089 / 25000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (451000788621 / 20000000000000 : ℝ))
      (E := (cell12673 ⟨52, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (20572392649089 / 25000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (451000788621 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_53 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (164511679327 / 200000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (1127503985619 / 50000000000000 : ℝ))
      (E := (cell12673 ⟨53, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (164511679327 / 200000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (1127503985619 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_54 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (82222132007807 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (28187649597 / 1250000000000 : ℝ))
      (E := (cell12673 ⟨54, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (82222132007807 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (28187649597 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_55 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (10273555950163 / 12500000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (90200639537 / 4000000000000 : ℝ))
      (E := (cell12673 ⟨55, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (10273555950163 / 12500000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (90200639537 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_56 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (82154786416161 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (3608031953 / 160000000000 : ℝ))
      (E := (cell12673 ⟨56, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (82154786416161 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (3608031953 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_57 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (41060574212343 / 50000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2255023969743 / 100000000000000 : ℝ))
      (E := (cell12673 ⟨57, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (41060574212343 / 50000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2255023969743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_58 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (82087533599323 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (56375699547 / 2500000000000 : ℝ))
      (E := (cell12673 ⟨58, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (82087533599323 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (56375699547 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_59 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (82053941912657 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (140939500183 / 6250000000000 : ℝ))
      (E := (cell12673 ⟨59, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (82053941912657 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (140939500183 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12674_40 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (20674041272829 / 25000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254832223027 / 100000000000000 : ℝ))
      (E := (cell12674 ⟨40, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (20674041272829 / 25000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254832223027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_41 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (82662152902473 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254836264171 / 100000000000000 : ℝ))
      (E := (cell12674 ⟨41, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (82662152902473 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254836264171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_42 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (82628164337219 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (1127420119531 / 50000000000000 : ℝ))
      (E := (cell12674 ⟨42, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (82628164337219 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (1127420119531 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_43 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (41297099682921 / 50000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (14092776653 / 625000000000 : ℝ))
      (E := (cell12674 ⟨43, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (41297099682921 / 50000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (14092776653 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_44 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (41280128979391 / 50000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (450969656131 / 20000000000000 : ℝ))
      (E := (cell12674 ⟨44, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (41280128979391 / 50000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (450969656131 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_45 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (41263170043313 / 50000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254852286371 / 100000000000000 : ℝ))
      (E := (cell12674 ⟨45, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (41263170043313 / 50000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254852286371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_46 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (8249244572011 / 10000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254856280193 / 100000000000000 : ℝ))
      (E := (cell12674 ⟨46, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (8249244572011 / 10000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254856280193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_47 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (20614643707529 / 25000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (281857532559 / 12500000000000 : ℝ))
      (E := (cell12674 ⟨47, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (20614643707529 / 25000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (281857532559 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_48 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (41212363693837 / 50000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (90194571371 / 4000000000000 : ℝ))
      (E := (cell12674 ⟨48, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (41212363693837 / 50000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (90194571371 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_49 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (82390903363959 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254868290639 / 100000000000000 : ℝ))
      (E := (cell12674 ⟨49, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (82390903363959 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254868290639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_50 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (82357102730289 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254872277271 / 100000000000000 : ℝ))
      (E := (cell12674 ⟨50, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (82357102730289 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254872277271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_51 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (82323325458127 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254876300671 / 100000000000000 : ℝ))
      (E := (cell12674 ⟨51, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (82323325458127 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254876300671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_52 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (2057239287977 / 2500000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (450976059833 / 20000000000000 : ℝ))
      (E := (cell12674 ⟨52, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (2057239287977 / 2500000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (450976059833 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_53 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (2570495027653 / 3125000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (563721082219 / 25000000000000 : ℝ))
      (E := (cell12674 ⟨53, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (2570495027653 / 3125000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (563721082219 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_54 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (82222133527463 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (450977665533 / 20000000000000 : ℝ))
      (E := (cell12674 ⟨54, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (82222133527463 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (450977665533 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_55 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (82188449418811 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (281861536523 / 12500000000000 : ℝ))
      (E := (cell12674 ⟨55, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (82188449418811 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (281861536523 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_56 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (82154788531111 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (1127448168559 / 50000000000000 : ℝ))
      (E := (cell12674 ⟨56, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (82154788531111 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (1127448168559 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_57 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (8212115083667 / 10000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (1127450170279 / 50000000000000 : ℝ))
      (E := (cell12674 ⟨57, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (8212115083667 / 10000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (1127450170279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_58 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (41043768153967 / 50000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254904298533 / 100000000000000 : ℝ))
      (E := (cell12674 ⟨58, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (41043768153967 / 50000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254904298533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_59 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (82053944917487 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (17616471291 / 781250000000 : ℝ))
      (E := (cell12674 ⟨59, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (82053944917487 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (17616471291 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

end BstLean.Part268
