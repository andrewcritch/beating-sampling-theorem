import BstLean.Part268CellShard1Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12375_40 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (10337126356013 / 12500000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (458746580333 / 20000000000000 : ℝ))
      (E := (cell12375 ⟨40, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (10337126356013 / 12500000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (458746580333 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_41 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (20665726547741 / 25000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293736921089 / 100000000000000 : ℝ))
      (E := (cell12375 ⟨41, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (20665726547741 / 25000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293736921089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_42 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (16525765057039 / 20000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293740895439 / 100000000000000 : ℝ))
      (E := (cell12375 ⟨42, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (16525765057039 / 20000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293740895439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_43 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (20648692025213 / 25000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (1146872441577 / 50000000000000 : ℝ))
      (E := (cell12375 ⟨43, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (20648692025213 / 25000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (1146872441577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_44 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (82560734608143 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (286718610467 / 12500000000000 : ℝ))
      (E := (cell12375 ⟨44, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (82560734608143 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (286718610467 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_45 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (41263362388713 / 50000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293752896469 / 100000000000000 : ℝ))
      (E := (cell12375 ⟨45, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (41263362388713 / 50000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293752896469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_46 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (8249273857921 / 10000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (1146878430781 / 50000000000000 : ℝ))
      (E := (cell12375 ⟨46, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (8249273857921 / 10000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (1146878430781 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_47 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (1649175519683 / 2000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293760895553 / 100000000000000 : ℝ))
      (E := (cell12375 ⟨47, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (1649175519683 / 2000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293760895553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_48 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (1648496739261 / 2000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293764879339 / 100000000000000 : ℝ))
      (E := (cell12375 ⟨48, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (1648496739261 / 2000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293764879339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_49 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (41195460743431 / 50000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293768870191 / 100000000000000 : ℝ))
      (E := (cell12375 ⟨49, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (41195460743431 / 50000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293768870191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_50 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (82357029526683 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293772866313 / 100000000000000 : ℝ))
      (E := (cell12375 ⟨50, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (82357029526683 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293772866313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_51 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (20580790263439 / 25000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (573444216423 / 25000000000000 : ℝ))
      (E := (cell12375 ⟨51, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (20580790263439 / 25000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (573444216423 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_52 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (20572329009867 / 25000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (1146890433051 / 50000000000000 : ℝ))
      (E := (cell12375 ⟨52, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (20572329009867 / 25000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (1146890433051 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_53 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (20563873613837 / 25000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (573446216277 / 25000000000000 : ℝ))
      (E := (cell12375 ⟨53, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (20563873613837 / 25000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (573446216277 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_54 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (82221696273071 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293788860059 / 100000000000000 : ℝ))
      (E := (cell12375 ⟨54, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (82221696273071 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293788860059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_55 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (82187921464451 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (458758581433 / 20000000000000 : ℝ))
      (E := (cell12375 ⟨55, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (82187921464451 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (458758581433 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_56 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (41077085000723 / 50000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293796885241 / 100000000000000 : ℝ))
      (E := (cell12375 ⟨56, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (41077085000723 / 50000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293796885241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_57 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (82120441856151 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293800909169 / 100000000000000 : ℝ))
      (E := (cell12375 ⟨57, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (82120441856151 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293800909169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_58 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (41043368500401 / 50000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (458760971451 / 20000000000000 : ℝ))
      (E := (cell12375 ⟨58, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (41043368500401 / 50000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (458760971451 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_59 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (3282122216311 / 4000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293808903219 / 100000000000000 : ℝ))
      (E := (cell12375 ⟨59, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (3282122216311 / 4000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293808903219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12376_40 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (82697007880381 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146797509547 / 50000000000000 : ℝ))
      (E := (cell12376 ⟨40, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (82697007880381 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146797509547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_41 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (41331451769111 / 50000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146799507041 / 50000000000000 : ℝ))
      (E := (cell12376 ⟨41, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (41331451769111 / 50000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146799507041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_42 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (82628822946997 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (229360296471 / 10000000000000 : ℝ))
      (E := (cell12376 ⟨42, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (82628822946997 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (229360296471 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_43 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (20648691519191 / 25000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293606988199 / 100000000000000 : ℝ))
      (E := (cell12376 ⟨43, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (20648691519191 / 25000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293606988199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_44 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (82560732897731 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146805483251 / 50000000000000 : ℝ))
      (E := (cell12376 ⟨44, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (82560732897731 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146805483251 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_45 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (2578960105633 / 3125000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293614957667 / 100000000000000 : ℝ))
      (E := (cell12376 ⟨45, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (2578960105633 / 3125000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293614957667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_46 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (82492737494849 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (573404740189 / 25000000000000 : ℝ))
      (E := (cell12376 ⟨46, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (82492737494849 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (573404740189 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_47 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (82458775212167 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146811487309 / 50000000000000 : ℝ))
      (E := (cell12376 ⟨47, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (82458775212167 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146811487309 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_48 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (41212418251507 / 50000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (458725399577 / 20000000000000 : ℝ))
      (E := (cell12376 ⟨48, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (41212418251507 / 50000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (458725399577 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_49 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (41195460669171 / 50000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146815485023 / 50000000000000 : ℝ))
      (E := (cell12376 ⟨49, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (41195460669171 / 50000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146815485023 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_50 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (329428118757 / 400000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (573408751783 / 25000000000000 : ℝ))
      (E := (cell12376 ⟨50, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (329428118757 / 400000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (573408751783 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_51 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (4116158076349 / 5000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146819494627 / 50000000000000 : ℝ))
      (E := (cell12376 ⟨51, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (4116158076349 / 5000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146819494627 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_52 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (82289316822921 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (286705371639 / 12500000000000 : ℝ))
      (E := (cell12376 ⟨52, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (82289316822921 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (286705371639 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_53 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (20563873887151 / 25000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (573411739067 / 25000000000000 : ℝ))
      (E := (cell12376 ⟨53, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (20563873887151 / 25000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (573411739067 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_54 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (41110848837851 / 50000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293650995117 / 100000000000000 : ℝ))
      (E := (cell12376 ⟨54, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (41110848837851 / 50000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293650995117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_55 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (2568372599251 / 3125000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146827484367 / 50000000000000 : ℝ))
      (E := (cell12376 ⟨55, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (2568372599251 / 3125000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146827484367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_56 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (82154172021551 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293658992159 / 100000000000000 : ℝ))
      (E := (cell12376 ⟨56, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (82154172021551 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293658992159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_57 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (20530111046089 / 25000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293663003069 / 100000000000000 : ℝ))
      (E := (cell12376 ⟨57, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (20530111046089 / 25000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293663003069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_58 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (82086739636683 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (286708374747 / 12500000000000 : ℝ))
      (E := (cell12376 ⟨58, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (82086739636683 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (286708374747 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_59 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (8205305835091 / 10000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293670973181 / 100000000000000 : ℝ))
      (E := (cell12376 ⟨59, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (8205305835091 / 10000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293670973181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12377_40 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (82697004913619 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (71670535407 / 3125000000000 : ℝ))
      (E := (cell12377 ⟨40, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (82697004913619 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (71670535407 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_41 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (82662900886401 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293461162357 / 100000000000000 : ℝ))
      (E := (cell12377 ⟨41, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (82662900886401 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293461162357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_42 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (82628820609683 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293465148087 / 100000000000000 : ℝ))
      (E := (cell12377 ⟨42, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (82628820609683 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293465148087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_43 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (1032434550669 / 1250000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (573367287163 / 25000000000000 : ℝ))
      (E := (cell12377 ⟨43, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (1032434550669 / 1250000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (573367287163 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_44 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (20640182797031 / 25000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293473163549 / 100000000000000 : ℝ))
      (E := (cell12377 ⟨44, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (20640182797031 / 25000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293473163549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_45 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (82526721983853 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293477133231 / 100000000000000 : ℝ))
      (E := (cell12377 ⟨45, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (82526721983853 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293477133231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_46 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (5155796025701 / 6250000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (573370278887 / 25000000000000 : ℝ))
      (E := (cell12377 ⟨46, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (5155796025701 / 6250000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (573370278887 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_47 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (82458774440873 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (71671409667 / 3125000000000 : ℝ))
      (E := (cell12377 ⟨47, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (82458774440873 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (71671409667 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_48 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (82424836043627 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293489113253 / 100000000000000 : ℝ))
      (E := (cell12377 ⟨48, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (82424836043627 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293489113253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_49 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (82390921190433 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293493125689 / 100000000000000 : ℝ))
      (E := (cell12377 ⟨49, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (82390921190433 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293493125689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_50 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (20589257463097 / 25000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293497144853 / 100000000000000 : ℝ))
      (E := (cell12377 ⟨50, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (20589257463097 / 25000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293497144853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_51 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (41161581000369 / 50000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (573375277439 / 25000000000000 : ℝ))
      (E := (cell12377 ⟨51, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (41161581000369 / 50000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (573375277439 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_52 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (8228931760687 / 10000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (1146752568049 / 50000000000000 : ℝ))
      (E := (cell12377 ⟨52, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (8228931760687 / 10000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (1146752568049 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_53 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (20563874160579 / 25000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (573377275867 / 25000000000000 : ℝ))
      (E := (cell12377 ⟨53, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (20563874160579 / 25000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (573377275867 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_54 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (82221699078751 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (1146756563617 / 50000000000000 : ℝ))
      (E := (cell12377 ⟨54, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (82221699078751 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (1146756563617 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_55 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (82187924887993 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293517145537 / 100000000000000 : ℝ))
      (E := (cell12377 ⟨55, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (82187924887993 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293517145537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_56 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (41077087020999 / 50000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (458704231061 / 20000000000000 : ℝ))
      (E := (cell12377 ⟨56, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (41077087020999 / 50000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (458704231061 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_57 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (2566263953527 / 3125000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293525153261 / 100000000000000 : ℝ))
      (E := (cell12377 ⟨57, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (2566263953527 / 3125000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293525153261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_58 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (8208674227283 / 10000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293529135911 / 100000000000000 : ℝ))
      (E := (cell12377 ⟨58, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (8208674227283 / 10000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293529135911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_59 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (82053061294271 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (573383289681 / 25000000000000 : ℝ))
      (E := (cell12377 ⟨59, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (82053061294271 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (573383289681 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12378_40 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (82697001947819 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293319360887 / 100000000000000 : ℝ))
      (E := (cell12378 ⟨40, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (82697001947819 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293319360887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_41 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (82662898235503 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (1146661682957 / 50000000000000 : ℝ))
      (E := (cell12378 ⟨41, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (82662898235503 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (1146661682957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_42 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (82628818273251 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293327386811 / 100000000000000 : ℝ))
      (E := (cell12378 ⟨42, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (82628818273251 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293327386811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_43 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (82594762031121 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293331364513 / 100000000000000 : ℝ))
      (E := (cell12378 ⟨43, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (82594762031121 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293331364513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_44 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (41280364739661 / 50000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (114666767863 / 5000000000000 : ℝ))
      (E := (cell12378 ⟨44, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (41280364739661 / 50000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (114666767863 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_45 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (16505344117643 / 20000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293339364333 / 100000000000000 : ℝ))
      (E := (cell12378 ⟨45, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (16505344117643 / 20000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293339364333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_46 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (82492735328311 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (458668676959 / 20000000000000 : ℝ))
      (E := (cell12378 ⟨46, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (82492735328311 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (458668676959 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_47 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (82458773670267 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293347358613 / 100000000000000 : ℝ))
      (E := (cell12378 ⟨47, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (82458773670267 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293347358613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_48 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (8242483558489 / 10000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293351343251 / 100000000000000 : ℝ))
      (E := (cell12378 ⟨48, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (8242483558489 / 10000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293351343251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_49 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (16478184208627 / 20000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293355337121 / 100000000000000 : ℝ))
      (E := (cell12378 ⟨49, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (16478184208627 / 20000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293355337121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_50 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (82357030016099 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (1146679669213 / 50000000000000 : ℝ))
      (E := (cell12378 ⟨50, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (82357030016099 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (1146679669213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_51 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (82323162475029 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293363345149 / 100000000000000 : ℝ))
      (E := (cell12378 ⟨51, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (82323162475029 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293363345149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_52 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (41144659195657 / 50000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293367355063 / 100000000000000 : ℝ))
      (E := (cell12378 ⟨52, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (41144659195657 / 50000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293367355063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_53 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (16451099547297 / 20000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (573342841433 / 25000000000000 : ℝ))
      (E := (cell12378 ⟨53, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (16451099547297 / 20000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (573342841433 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_54 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (82221700482219 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (4586750749 / 200000000000 : ℝ))
      (E := (cell12378 ⟨54, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (82221700482219 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (4586750749 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_55 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (82187926600333 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293379378509 / 100000000000000 : ℝ))
      (E := (cell12378 ⟨55, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (82187926600333 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293379378509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_56 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (41077088031393 / 50000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (573345843671 / 25000000000000 : ℝ))
      (E := (cell12378 ⟨56, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (41077088031393 / 50000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (573345843671 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_57 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (20530112210419 / 25000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (1146693679873 / 50000000000000 : ℝ))
      (E := (cell12378 ⟨57, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (20530112210419 / 25000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (1146693679873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_58 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (82086744909241 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (458678266041 / 20000000000000 : ℝ))
      (E := (cell12378 ⟨58, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (82086744909241 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (458678266041 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_59 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (82053064237859 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (573348835381 / 25000000000000 : ℝ))
      (E := (cell12378 ⟨59, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (82053064237859 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (573348835381 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12379_40 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (82696998982979 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293181643971 / 100000000000000 : ℝ))
      (E := (cell12379 ⟨40, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (82696998982979 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293181643971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_41 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (82662895585527 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146592812377 / 50000000000000 : ℝ))
      (E := (cell12379 ⟨41, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (82662895585527 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146592812377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_42 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (82628815937703 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146594811059 / 50000000000000 : ℝ))
      (E := (cell12379 ⟨42, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (82628815937703 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146594811059 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_43 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (16518952001913 / 20000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146596817893 / 50000000000000 : ℝ))
      (E := (cell12379 ⟨43, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (16518952001913 / 20000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146596817893 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_44 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (3302429110853 / 4000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146598832627 / 50000000000000 : ℝ))
      (E := (cell12379 ⟨44, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (3302429110853 / 4000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146598832627 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_45 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (322369996849 / 390625000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293201650971 / 100000000000000 : ℝ))
      (E := (cell12379 ⟨45, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (322369996849 / 390625000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293201650971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_46 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (20623183561533 / 25000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293205650787 / 100000000000000 : ℝ))
      (E := (cell12379 ⟨46, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (20623183561533 / 25000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293205650787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_47 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (82458772900349 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293209663547 / 100000000000000 : ℝ))
      (E := (cell12379 ⟨47, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (82458772900349 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293209663547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_48 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (82424835126803 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (143325851811 / 6250000000000 : ℝ))
      (E := (cell12379 ⟨48, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (82424835126803 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (143325851811 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_49 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (82390920896447 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (286652207909 / 12500000000000 : ℝ))
      (E := (cell12379 ⟨49, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (82390920896447 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (286652207909 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_50 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (41178515090191 / 50000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (573305411701 / 25000000000000 : ℝ))
      (E := (cell12379 ⟨50, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (41178515090191 / 50000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (573305411701 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_51 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (41161581474927 / 50000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293225636459 / 100000000000000 : ℝ))
      (E := (cell12379 ⟨51, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (41161581474927 / 50000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293225636459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_52 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (20572329794063 / 25000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (229322963001 / 10000000000000 : ℝ))
      (E := (cell12379 ⟨52, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (20572329794063 / 25000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (229322963001 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_53 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (8225549883111 / 10000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146616812509 / 50000000000000 : ℝ))
      (E := (cell12379 ⟨53, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (8225549883111 / 10000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146616812509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_54 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (10277712735763 / 12500000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293237618829 / 100000000000000 : ℝ))
      (E := (cell12379 ⟨54, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (10277712735763 / 12500000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293237618829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_55 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (82187928313053 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293241608581 / 100000000000000 : ℝ))
      (E := (cell12379 ⟨55, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (82187928313053 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293241608581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_56 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (16430835616783 / 20000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (458649130059 / 20000000000000 : ℝ))
      (E := (cell12379 ⟨56, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (16430835616783 / 20000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (458649130059 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_57 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (8212045117079 / 10000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293249622527 / 100000000000000 : ℝ))
      (E := (cell12379 ⟨57, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (8212045117079 / 10000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293249622527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_58 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (82086747545917 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146626819997 / 50000000000000 : ℝ))
      (E := (cell12379 ⟨58, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (82086747545917 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146626819997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_59 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (41026533590837 / 50000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293257639907 / 100000000000000 : ℝ))
      (E := (cell12379 ⟨59, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (41026533590837 / 50000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293257639907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12380_40 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (82696996019101 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (91721759291 / 4000000000000 : ℝ))
      (E := (cell12380 ⟨40, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (82696996019101 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (91721759291 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_41 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (82662892936473 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293047997617 / 100000000000000 : ℝ))
      (E := (cell12380 ⟨41, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (82662892936473 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293047997617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_42 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (82628813603037 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293051971537 / 100000000000000 : ℝ))
      (E := (cell12380 ⟨42, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (82628813603037 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293051971537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_43 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (82594757988853 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (286632002657 / 12500000000000 : ℝ))
      (E := (cell12380 ⟨43, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (82594757988853 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (286632002657 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_44 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (20640181516033 / 25000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (1146529984957 / 50000000000000 : ℝ))
      (E := (cell12380 ⟨44, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (20640181516033 / 25000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (1146529984957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_45 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (82526717799237 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (45861279863 / 2000000000000 : ℝ))
      (E := (cell12380 ⟨45, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (82526717799237 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (45861279863 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_46 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (2062318329117 / 2500000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (1146533986191 / 50000000000000 : ℝ))
      (E := (cell12380 ⟨46, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (2062318329117 / 2500000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (1146533986191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_47 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (82458772131119 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293071965267 / 100000000000000 : ℝ))
      (E := (cell12380 ⟨47, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (82458772131119 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293071965267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_48 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (20606208667341 / 25000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293075970431 / 100000000000000 : ℝ))
      (E := (cell12380 ⟨48, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (20606208667341 / 25000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293075970431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_49 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (8239092075037 / 10000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (143317499143 / 6250000000000 : ℝ))
      (E := (cell12380 ⟨49, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (8239092075037 / 10000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (143317499143 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_50 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (82357030345237 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293084011037 / 100000000000000 : ℝ))
      (E := (cell12380 ⟨50, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (82357030345237 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293084011037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_51 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (20580790856303 / 25000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293087983687 / 100000000000000 : ℝ))
      (E := (cell12380 ⟨51, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (20580790856303 / 25000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293087983687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_52 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (16457863992337 / 20000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (1146545980469 / 50000000000000 : ℝ))
      (E := (cell12380 ⟨52, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (16457863992337 / 20000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (1146545980469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_53 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (5140968745387 / 6250000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293095999369 / 100000000000000 : ℝ))
      (E := (cell12380 ⟨53, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (5140968745387 / 6250000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293095999369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_54 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (10277712911301 / 12500000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293099978309 / 100000000000000 : ℝ))
      (E := (cell12380 ⟨54, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (10277712911301 / 12500000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293099978309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_55 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (10273491253269 / 12500000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293103953893 / 100000000000000 : ℝ))
      (E := (cell12380 ⟨55, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (10273491253269 / 12500000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293103953893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_56 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (16430836021077 / 20000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293107982139 / 100000000000000 : ℝ))
      (E := (cell12380 ⟨56, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (16430836021077 / 20000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293107982139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_57 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (82120453500207 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (28663900009 / 1250000000000 : ℝ))
      (E := (cell12380 ⟨57, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (82120453500207 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (28663900009 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_58 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (41043375091429 / 50000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293116006143 / 100000000000000 : ℝ))
      (E := (cell12380 ⟨58, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (41043375091429 / 50000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293116006143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_59 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (16410614025143 / 20000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293119994711 / 100000000000000 : ℝ))
      (E := (cell12380 ⟨59, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (16410614025143 / 20000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293119994711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12381_40 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (82696993056183 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (573226608629 / 25000000000000 : ℝ))
      (E := (cell12381 ⟨40, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (82696993056183 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (573226608629 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_41 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (4133144514417 / 5000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (1146455212883 / 50000000000000 : ℝ))
      (E := (cell12381 ⟨41, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (4133144514417 / 5000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (1146455212883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_42 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (82628811269253 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292914435067 / 100000000000000 : ℝ))
      (E := (cell12381 ⟨42, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (82628811269253 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292914435067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_43 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (10324344496123 / 12500000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292918403353 / 100000000000000 : ℝ))
      (E := (cell12381 ⟨43, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (10324344496123 / 12500000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292918403353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_44 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (5160045272359 / 6250000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (114646119443 / 5000000000000 : ℝ))
      (E := (cell12381 ⟨44, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (5160045272359 / 6250000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (114646119443 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_45 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (82526716405897 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292926390867 / 100000000000000 : ℝ))
      (E := (cell12381 ⟨45, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (82526716405897 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292926390867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_46 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (41246366041977 / 50000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292930408437 / 100000000000000 : ℝ))
      (E := (cell12381 ⟨46, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (41246366041977 / 50000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292930408437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_47 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (82458771362577 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292934381533 / 100000000000000 : ℝ))
      (E := (cell12381 ⟨47, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (82458771362577 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292934381533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_48 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (3296993368503 / 4000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292938426519 / 100000000000000 : ℝ))
      (E := (cell12381 ⟨48, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (3296993368503 / 4000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292938426519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_49 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (82390920604903 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (286617803003 / 12500000000000 : ℝ))
      (E := (cell12381 ⟨49, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (82390920604903 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (286617803003 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_50 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (82357030510663 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (143309148261 / 6250000000000 : ℝ))
      (E := (cell12381 ⟨50, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (82357030510663 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (143309148261 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_51 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (82323163901103 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (458590077367 / 20000000000000 : ℝ))
      (E := (cell12381 ⟨51, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (82323163901103 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (458590077367 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_52 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (82289320747613 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (1146477203423 / 50000000000000 : ℝ))
      (E := (cell12381 ⟨52, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (82289320747613 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (1146477203423 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_53 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (82255501021729 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (458591674149 / 20000000000000 : ℝ))
      (E := (cell12381 ⟨53, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (82255501021729 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (458591674149 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_54 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (10277713086891 / 12500000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292962393899 / 100000000000000 : ℝ))
      (E := (cell12381 ⟨54, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (10277713086891 / 12500000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292962393899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_55 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (82187931739631 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (573241603611 / 25000000000000 : ℝ))
      (E := (cell12381 ⟨55, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (82187931739631 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (573241603611 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_56 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (82154182127197 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292970370217 / 100000000000000 : ℝ))
      (E := (cell12381 ⟨56, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (82154182127197 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292970370217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_57 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (82120455829927 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292974376093 / 100000000000000 : ℝ))
      (E := (cell12381 ⟨57, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (82120455829927 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292974376093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_58 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (82086752820063 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (286622296189 / 12500000000000 : ℝ))
      (E := (cell12381 ⟨58, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (82086752820063 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (286622296189 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_59 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (82053073069983 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292982405937 / 100000000000000 : ℝ))
      (E := (cell12381 ⟨59, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (82053073069983 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292982405937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12382_40 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (3307879603769 / 4000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (1146384441633 / 50000000000000 : ℝ))
      (E := (cell12382 ⟨40, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (3307879603769 / 4000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (1146384441633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_41 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (10332860955141 / 12500000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (1146386454601 / 50000000000000 : ℝ))
      (E := (cell12382 ⟨41, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (10332860955141 / 12500000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (1146386454601 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_42 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (2582150279261 / 3125000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (458555379037 / 20000000000000 : ℝ))
      (E := (cell12382 ⟨42, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (2582150279261 / 3125000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (458555379037 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_43 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (41297376974979 / 50000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (45855617993 / 2000000000000 : ℝ))
      (E := (cell12382 ⟨43, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (41297376974979 / 50000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (45855617993 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_44 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (16125141143 / 19531250000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292784863283 / 100000000000000 : ℝ))
      (E := (cell12382 ⟨44, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (16125141143 / 19531250000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292784863283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_45 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (82526715013321 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292788902959 / 100000000000000 : ℝ))
      (E := (cell12382 ⟨45, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (82526715013321 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292788902959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_46 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (16498546200791 / 20000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (4478111133 / 195312500000 : ℝ))
      (E := (cell12382 ⟨46, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (16498546200791 / 20000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (4478111133 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_47 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (41229385297361 / 50000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292796853467 / 100000000000000 : ℝ))
      (E := (cell12382 ⟨47, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (41229385297361 / 50000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292796853467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_48 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (41212416878217 / 50000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (1146400439717 / 50000000000000 : ℝ))
      (E := (cell12382 ⟨48, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (41212416878217 / 50000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (1146400439717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_49 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (41195460230023 / 50000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292804858627 / 100000000000000 : ℝ))
      (E := (cell12382 ⟨49, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (41195460230023 / 50000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292804858627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_50 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (82357030676661 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292808848123 / 100000000000000 : ℝ))
      (E := (cell12382 ⟨50, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (82357030676661 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292808848123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_51 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (41161582188763 / 50000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (143300802869 / 6250000000000 : ℝ))
      (E := (cell12382 ⟨51, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (41161582188763 / 50000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (143300802869 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_52 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (16457864306807 / 20000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (114640842487 / 5000000000000 : ℝ))
      (E := (cell12382 ⟨52, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (16457864306807 / 20000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (114640842487 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_53 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (41127751058861 / 50000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (229282085719 / 10000000000000 : ℝ))
      (E := (cell12382 ⟨53, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (41127751058861 / 50000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (229282085719 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_54 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (41110853050133 / 50000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (1146412432799 / 50000000000000 : ℝ))
      (E := (cell12382 ⟨54, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (41110853050133 / 50000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (1146412432799 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_55 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (5136745840843 / 6250000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (22928288721 / 1000000000000 : ℝ))
      (E := (cell12382 ⟨55, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (5136745840843 / 6250000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (22928288721 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_56 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (82154184149349 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (1146416436811 / 50000000000000 : ℝ))
      (E := (cell12382 ⟨56, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (82154184149349 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (1146416436811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_57 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (1642409163199 / 2000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (7165115209 / 312500000000 : ℝ))
      (E := (cell12382 ⟨57, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (1642409163199 / 2000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (7165115209 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_58 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (20521688864383 / 25000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (1146420424191 / 50000000000000 : ℝ))
      (E := (cell12382 ⟨58, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (20521688864383 / 25000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (1146420424191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_59 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (82053076014477 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292844873587 / 100000000000000 : ℝ))
      (E := (cell12382 ⟨59, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (82053076014477 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292844873587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12383_40 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (82696987133227 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (573157861489 / 25000000000000 : ℝ))
      (E := (cell12383 ⟨40, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (82696987133227 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (573157861489 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_41 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (82662884994837 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292635389187 / 100000000000000 : ℝ))
      (E := (cell12383 ⟨41, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (82662884994837 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292635389187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_42 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (20657201651083 / 25000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (458527882131 / 20000000000000 : ℝ))
      (E := (cell12383 ⟨42, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (20657201651083 / 25000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (458527882131 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_43 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (41297375965887 / 50000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292643392577 / 100000000000000 : ℝ))
      (E := (cell12383 ⟨43, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (41297375965887 / 50000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292643392577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_44 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (82560720947379 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (1146323696593 / 50000000000000 : ℝ))
      (E := (cell12383 ⟨44, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (82560720947379 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (1146323696593 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_45 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (8252671362151 / 10000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292651411761 / 100000000000000 : ℝ))
      (E := (cell12383 ⟨45, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (8252671362151 / 10000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292651411761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_46 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (82492729924681 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (458531077701 / 20000000000000 : ℝ))
      (E := (cell12383 ⟨46, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (82492729924681 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (458531077701 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_47 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (16491753965511 / 20000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292659381069 / 100000000000000 : ℝ))
      (E := (cell12383 ⟨47, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (16491753965511 / 20000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292659381069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_48 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (41212416650471 / 50000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (1146331694041 / 50000000000000 : ℝ))
      (E := (cell12383 ⟨48, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (41212416650471 / 50000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (1146331694041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_49 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (82390920315799 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (1146333703977 / 50000000000000 : ℝ))
      (E := (cell12383 ⟨49, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (82390920315799 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (1146333703977 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_50 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (8235703084323 / 10000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292671379929 / 100000000000000 : ℝ))
      (E := (cell12383 ⟨50, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (8235703084323 / 10000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292671379929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_51 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (82323164854483 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292675419869 / 100000000000000 : ℝ))
      (E := (cell12383 ⟨51, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (82323164854483 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292675419869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_52 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (82289322320951 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292679407617 / 100000000000000 : ℝ))
      (E := (cell12383 ⟨52, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (82289322320951 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292679407617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_53 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (82255503214171 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (1146341699841 / 50000000000000 : ℝ))
      (E := (cell12383 ⟨53, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (82255503214171 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (1146341699841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_54 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (41110853752911 / 50000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (17911620261 / 781250000000 : ℝ))
      (E := (cell12383 ⟨54, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (41110853752911 / 50000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (17911620261 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_55 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (3287517406709 / 4000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (229269138593 / 10000000000000 : ℝ))
      (E := (cell12383 ⟨55, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (3287517406709 / 4000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (229269138593 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_56 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (82154186171841 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292695374173 / 100000000000000 : ℝ))
      (E := (cell12383 ⟨56, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (82154186171841 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292695374173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_57 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (3284818419611 / 4000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292699413967 / 100000000000000 : ℝ))
      (E := (cell12383 ⟨57, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (3284818419611 / 4000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292699413967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_58 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (41043379047633 / 50000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292703383613 / 100000000000000 : ℝ))
      (E := (cell12383 ⟨58, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (41043379047633 / 50000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292703383613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_59 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (82053078959197 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292707397663 / 100000000000000 : ℝ))
      (E := (cell12383 ⟨59, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (82053078959197 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292707397663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12384_40 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (82696984173189 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (573123501289 / 25000000000000 : ℝ))
      (E := (cell12384 ⟨40, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (82696984173189 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (573123501289 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_41 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (41331441174733 / 50000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (114624902097 / 5000000000000 : ℝ))
      (E := (cell12384 ⟨41, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (41331441174733 / 50000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (114624902097 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_42 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (82628804273193 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (1146251020121 / 50000000000000 : ℝ))
      (E := (cell12384 ⟨42, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (82628804273193 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (1146251020121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_43 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (41297374957217 / 50000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (1146252999853 / 50000000000000 : ℝ))
      (E := (cell12384 ⟨43, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (41297374957217 / 50000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (1146252999853 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_44 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (41280359621701 / 50000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292510037379 / 100000000000000 : ℝ))
      (E := (cell12384 ⟨44, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (41280359621701 / 50000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292510037379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_45 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (1289479878601 / 1562500000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292514034939 / 100000000000000 : ℝ))
      (E := (cell12384 ⟨45, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (1289479878601 / 1562500000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292514034939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_46 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (82492728846133 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292517991377 / 100000000000000 : ℝ))
      (E := (cell12384 ⟨46, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (82492728846133 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292517991377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_47 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (41229384530537 / 50000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (286565252903 / 12500000000000 : ℝ))
      (E := (cell12384 ⟨47, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (41229384530537 / 50000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (286565252903 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_48 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (82424832846097 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292526011369 / 100000000000000 : ℝ))
      (E := (cell12384 ⟨48, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (82424832846097 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292526011369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_49 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (82390920172161 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292530013077 / 100000000000000 : ℝ))
      (E := (cell12384 ⟨49, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (82390920172161 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292530013077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_50 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (82357031010369 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292534026547 / 100000000000000 : ℝ))
      (E := (cell12384 ⟨50, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (82357031010369 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292534026547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_51 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (82323165331971 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292537990783 / 100000000000000 : ℝ))
      (E := (cell12384 ⟨51, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (82323165331971 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292537990783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_52 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (82289323108361 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292542021481 / 100000000000000 : ℝ))
      (E := (cell12384 ⟨52, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (82289323108361 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292542021481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_53 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (3290220172443 / 4000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (143284124889 / 6250000000000 : ℝ))
      (E := (cell12384 ⟨53, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (3290220172443 / 4000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (143284124889 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_54 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (41110854455897 / 50000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (229254997733 / 10000000000000 : ℝ))
      (E := (cell12384 ⟨54, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (41110854455897 / 50000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (229254997733 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_55 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (4109396844117 / 5000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292554015003 / 100000000000000 : ℝ))
      (E := (cell12384 ⟨55, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (4109396844117 / 5000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292554015003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_56 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (3286167527787 / 4000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (573139497513 / 25000000000000 : ℝ))
      (E := (cell12384 ⟨56, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (3286167527787 / 4000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (573139497513 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_57 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (41060231410451 / 50000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (458512403471 / 20000000000000 : ℝ))
      (E := (cell12384 ⟨57, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (41060231410451 / 50000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (458512403471 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_58 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (5130422545829 / 6250000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292565975207 / 100000000000000 : ℝ))
      (E := (cell12384 ⟨58, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (5130422545829 / 6250000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292565975207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_59 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (82053081904143 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292569978163 / 100000000000000 : ℝ))
      (E := (cell12384 ⟨59, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (82053081904143 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292569978163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12385_40 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (82696981214111 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292356678297 / 100000000000000 : ℝ))
      (E := (cell12385 ⟨40, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (82696981214111 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292356678297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_41 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (10332859963127 / 12500000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292360691243 / 100000000000000 : ℝ))
      (E := (cell12385 ⟨41, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (10332859963127 / 12500000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292360691243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_42 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (10328600242867 / 12500000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292364666419 / 100000000000000 : ℝ))
      (E := (cell12385 ⟨42, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (10328600242867 / 12500000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292364666419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_43 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (16518949579587 / 20000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292368662253 / 100000000000000 : ℝ))
      (E := (cell12385 ⟨43, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (16518949579587 / 20000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292368662253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_44 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (20640179385057 / 25000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (1146186339121 / 50000000000000 : ℝ))
      (E := (cell12385 ⟨44, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (20640179385057 / 25000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (1146186339121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_45 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (41263355420091 / 50000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (573094163707 / 25000000000000 : ℝ))
      (E := (cell12385 ⟨45, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (41263355420091 / 50000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (573094163707 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_46 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (82492727768311 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (17909223827 / 781250000000 : ℝ))
      (E := (cell12385 ⟨46, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (82492727768311 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (17909223827 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_47 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (1030734603691 / 1250000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (286548082771 / 12500000000000 : ℝ))
      (E := (cell12385 ⟨47, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (1030734603691 / 1250000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (286548082771 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_48 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (82424832391901 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (573097172597 / 25000000000000 : ℝ))
      (E := (cell12385 ⟨48, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (82424832391901 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (573097172597 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_49 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (82390920029133 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292392673997 / 100000000000000 : ℝ))
      (E := (cell12385 ⟨49, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (82390920029133 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292392673997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_50 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (514731444863 / 625000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292396670073 / 100000000000000 : ℝ))
      (E := (cell12385 ⟨50, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (514731444863 / 625000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292396670073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_51 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (10290395726249 / 12500000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (458480135319 / 20000000000000 : ℝ))
      (E := (cell12385 ⟨51, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (10290395726249 / 12500000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (458480135319 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_52 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (10286165487033 / 12500000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292404691331 / 100000000000000 : ℝ))
      (E := (cell12385 ⟨52, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (10286165487033 / 12500000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292404691331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_53 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (16451101081687 / 20000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (1146204326407 / 50000000000000 : ℝ))
      (E := (cell12385 ⟨53, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (16451101081687 / 20000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (1146204326407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_54 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (10277713789773 / 12500000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292412676409 / 100000000000000 : ℝ))
      (E := (cell12385 ⟨54, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (10277713789773 / 12500000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292412676409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_55 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (82187938597333 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292416641183 / 100000000000000 : ℝ))
      (E := (cell12385 ⟨55, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (82187938597333 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292416641183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_56 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (10269273777231 / 12500000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292420662171 / 100000000000000 : ℝ))
      (E := (cell12385 ⟨56, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (10269273777231 / 12500000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292420662171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_57 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (82120465151831 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292424677043 / 100000000000000 : ℝ))
      (E := (cell12385 ⟨57, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (82120465151831 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292424677043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_58 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (41043381685763 / 50000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (458485736461 / 20000000000000 : ℝ))
      (E := (cell12385 ⟨58, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (41043381685763 / 50000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (458485736461 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_59 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (41026542424657 / 50000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (1146216337127 / 50000000000000 : ℝ))
      (E := (cell12385 ⟨59, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (41026542424657 / 50000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (1146216337127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12386_40 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (82696978255991 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292219406667 / 100000000000000 : ℝ))
      (E := (cell12386 ⟨40, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (82696978255991 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292219406667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_41 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (41331438530743 / 50000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146111697919 / 50000000000000 : ℝ))
      (E := (cell12386 ⟨41, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (41331438530743 / 50000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146111697919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_42 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (2065719990339 / 2500000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292227406713 / 100000000000000 : ℝ))
      (E := (cell12386 ⟨42, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (2065719990339 / 2500000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292227406713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_43 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (41297372941139 / 50000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146115690109 / 50000000000000 : ℝ))
      (E := (cell12386 ⟨43, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (41297372941139 / 50000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146115690109 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_44 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (82560715837857 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292235374587 / 100000000000000 : ℝ))
      (E := (cell12386 ⟨44, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (82560715837857 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292235374587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_45 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (10315838681333 / 12500000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (286529923637 / 12500000000000 : ℝ))
      (E := (cell12386 ⟨45, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (10315838681333 / 12500000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (286529923637 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_46 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (41246363345607 / 50000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146121711401 / 50000000000000 : ℝ))
      (E := (cell12386 ⟨46, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (41246363345607 / 50000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146121711401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_47 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (82458767530173 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (458449483133 / 20000000000000 : ℝ))
      (E := (cell12386 ⟨47, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (82458767530173 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (458449483133 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_48 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (82424831938353 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146125683119 / 50000000000000 : ℝ))
      (E := (cell12386 ⟨48, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (82424831938353 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146125683119 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_49 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (82390919886713 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292255390717 / 100000000000000 : ℝ))
      (E := (cell12386 ⟨49, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (82390919886713 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292255390717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_50 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (2058925783659 / 2500000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146129684731 / 50000000000000 : ℝ))
      (E := (cell12386 ⟨50, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (2058925783659 / 2500000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146129684731 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_51 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (16464633257709 / 20000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292263418331 / 100000000000000 : ℝ))
      (E := (cell12386 ⟨51, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (16464633257709 / 20000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292263418331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_52 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (82289324684661 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292267417169 / 100000000000000 : ℝ))
      (E := (cell12386 ⟨52, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (82289324684661 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292267417169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_53 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (82255506506249 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (17908370027 / 781250000000 : ℝ))
      (E := (cell12386 ⟨53, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (82255506506249 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (17908370027 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_54 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (82221711724989 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146137686279 / 50000000000000 : ℝ))
      (E := (cell12386 ⟨54, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (82221711724989 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146137686279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_55 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (16437588062541 / 20000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (143267461413 / 6250000000000 : ℝ))
      (E := (cell12386 ⟨55, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (16437588062541 / 20000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (143267461413 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_56 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (82154192241361 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292283390529 / 100000000000000 : ℝ))
      (E := (cell12386 ⟨56, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (82154192241361 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292283390529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_57 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (41060233741531 / 50000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146143696517 / 50000000000000 : ℝ))
      (E := (cell12386 ⟨57, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (41060233741531 / 50000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146143696517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_58 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (82086766010051 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (573072846657 / 25000000000000 : ℝ))
      (E := (cell12386 ⟨58, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (82086766010051 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (573072846657 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_59 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (10256635974339 / 12500000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (286536920951 / 12500000000000 : ℝ))
      (E := (cell12386 ⟨59, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (10256635974339 / 12500000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (286536920951 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12387_40 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (8269697529883 / 10000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292082190267 / 100000000000000 : ℝ))
      (E := (cell12387 ⟨40, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (8269697529883 / 10000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292082190267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_41 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (661302995351 / 800000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292086214467 / 100000000000000 : ℝ))
      (E := (cell12387 ⟨41, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (661302995351 / 800000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292086214467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_42 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (10328599660633 / 12500000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (1146045101183 / 50000000000000 : ℝ))
      (E := (cell12387 ⟨42, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (10328599660633 / 12500000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (1146045101183 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_43 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (82594743867463 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292094212391 / 100000000000000 : ℝ))
      (E := (cell12387 ⟨43, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (82594743867463 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292094212391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_44 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (82560714136289 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (573024546307 / 25000000000000 : ℝ))
      (E := (cell12387 ⟨44, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (82560714136289 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (573024546307 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_45 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (8252670806191 / 10000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (71628193091 / 3125000000000 : ℝ))
      (E := (cell12387 ⟨45, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (8252670806191 / 10000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (71628193091 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_46 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (41246362807421 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (1146053096251 / 50000000000000 : ℝ))
      (E := (cell12387 ⟨46, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (41246362807421 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (1146053096251 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_47 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (82458766765751 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292110165957 / 100000000000000 : ℝ))
      (E := (cell12387 ⟨47, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (82458766765751 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292110165957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_48 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (20606207871363 / 25000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (573028539183 / 25000000000000 : ℝ))
      (E := (cell12387 ⟨48, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (20606207871363 / 25000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (573028539183 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_49 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (82390919744903 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292118163237 / 100000000000000 : ℝ))
      (E := (cell12387 ⟨49, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (82390919744903 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292118163237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_50 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (20589257878803 / 25000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (458424436733 / 20000000000000 : ℝ))
      (E := (cell12387 ⟨50, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (20589257878803 / 25000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (458424436733 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_51 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (82323166767629 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292126157021 / 100000000000000 : ℝ))
      (E := (cell12387 ⟨51, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (82323166767629 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292126157021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_52 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (5143082842097 / 6250000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (573032549749 / 25000000000000 : ℝ))
      (E := (cell12387 ⟨52, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (5143082842097 / 6250000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (573032549749 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_53 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (82255507604519 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292134189173 / 100000000000000 : ℝ))
      (E := (cell12387 ⟨53, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (82255507604519 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292134189173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_54 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (20555428283053 / 25000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292138183867 / 100000000000000 : ℝ))
      (E := (cell12387 ⟨54, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (20555428283053 / 25000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292138183867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_55 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (10273492753557 / 12500000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (573035545053 / 25000000000000 : ℝ))
      (E := (cell12387 ⟨55, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (10273492753557 / 12500000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (573035545053 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_56 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (16430838853043 / 20000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (286518271891 / 12500000000000 : ℝ))
      (E := (cell12387 ⟨56, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (16430838853043 / 20000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (286518271891 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_57 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (16424093962919 / 20000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292150165329 / 100000000000000 : ℝ))
      (E := (cell12387 ⟨57, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (16424093962919 / 20000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292150165329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_58 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (2052169216221 / 2500000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292154147319 / 100000000000000 : ℝ))
      (E := (cell12387 ⟨58, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (2052169216221 / 2500000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292154147319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_59 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (16410618148067 / 20000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (458431635311 / 20000000000000 : ℝ))
      (E := (cell12387 ⟨59, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (16410618148067 / 20000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (458431635311 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12388_40 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (20674243085657 / 25000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291945029097 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨40, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (20674243085657 / 25000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291945029097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_41 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (82662871777183 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291949029651 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨41, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (82662871777183 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291949029651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_42 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (10328599369681 / 12500000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (35811766459 / 1562500000000 : ℝ))
      (E := (cell12388 ⟨42, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (10328599369681 / 12500000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (35811766459 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_43 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (82594741853489 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291957041199 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨43, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (82594741853489 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291957041199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_44 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (82560712435523 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (286495131419 / 12500000000000 : ℝ))
      (E := (cell12388 ⟨44, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (82560712435523 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (286495131419 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_45 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (82526706673919 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (572991256069 / 25000000000000 : ℝ))
      (E := (cell12388 ⟨45, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (82526706673919 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (572991256069 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_46 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (16498544907839 / 20000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291969017813 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨46, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (16498544907839 / 20000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291969017813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_47 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (2576836437563 / 3125000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291973030803 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨47, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (2576836437563 / 3125000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291973030803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_48 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (41212415516599 / 50000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291977002963 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨48, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (41212415516599 / 50000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291977002963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_49 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (82390919603701 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291981050487 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨49, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (82390919603701 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291981050487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_50 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (82357031684633 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291985053733 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨50, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (82357031684633 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291985053733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_51 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (16464633449449 / 20000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291989010613 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨51, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (16464633449449 / 20000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291989010613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_52 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (16457865252587 / 20000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (458398607363 / 20000000000000 : ℝ))
      (E := (cell12388 ⟨52, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (16457865252587 / 20000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (458398607363 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_53 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (82255508703243 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291997011921 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨53, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (82255508703243 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291997011921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_54 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (82221714539851 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2292001051293 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨54, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (82221714539851 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2292001051293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_55 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (10273492968073 / 12500000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (458401006799 / 20000000000000 : ℝ))
      (E := (cell12388 ⟨55, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (10273492968073 / 12500000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (458401006799 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_56 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (641829658511 / 781250000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (229200901597 / 10000000000000 : ℝ))
      (E := (cell12388 ⟨56, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (641829658511 / 781250000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (229200901597 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_57 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (82120472146429 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (458402610609 / 20000000000000 : ℝ))
      (E := (cell12388 ⟨57, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (82120472146429 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (458402610609 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_58 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (82086771287893 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (458403404703 / 20000000000000 : ℝ))
      (E := (cell12388 ⟨58, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (82086771287893 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (458403404703 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_59 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (82053093686183 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2292021041933 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨59, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (82053093686183 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2292021041933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12389_40 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (82696969387383 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291807923159 / 100000000000000 : ℝ))
      (E := (cell12389 ⟨40, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (82696969387383 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291807923159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_41 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (82662869136411 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291811958869 / 100000000000000 : ℝ))
      (E := (cell12389 ⟨41, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (82662869136411 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291811958869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_42 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (82628792630713 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (458363191949 / 20000000000000 : ℝ))
      (E := (cell12389 ⟨42, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (82628792630713 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (458363191949 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_43 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (20648684960089 / 25000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291819925429 / 100000000000000 : ℝ))
      (E := (cell12389 ⟨43, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (20648684960089 / 25000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291819925429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_44 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (82560710735559 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291823972963 / 100000000000000 : ℝ))
      (E := (cell12389 ⟨44, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (82560710735559 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291823972963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_45 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (20631676321673 / 25000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291827925189 / 100000000000000 : ℝ))
      (E := (cell12389 ⟨45, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (20631676321673 / 25000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291827925189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_46 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (5155795216517 / 6250000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (1145915978797 / 50000000000000 : ℝ))
      (E := (cell12389 ⟨46, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (5155795216517 / 6250000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (1145915978797 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_47 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (82458765238967 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (91673438053 / 4000000000000 : ℝ))
      (E := (cell12389 ⟨47, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (82458765238967 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (91673438053 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_48 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (10303103822699 / 12500000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291839963837 / 100000000000000 : ℝ))
      (E := (cell12389 ⟨48, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (10303103822699 / 12500000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291839963837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_49 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (20597729865777 / 25000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (229184393461 / 10000000000000 : ℝ))
      (E := (cell12389 ⟨49, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (20597729865777 / 25000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (229184393461 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_50 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (2573657245457 / 3125000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (572961980179 / 25000000000000 : ℝ))
      (E := (cell12389 ⟨50, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (2573657245457 / 3125000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (572961980179 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_51 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (82323167727393 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (572962980033 / 25000000000000 : ℝ))
      (E := (cell12389 ⟨51, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (82323167727393 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (572962980033 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_52 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (20572331763203 / 25000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (8952562229 / 390625000000 : ℝ))
      (E := (cell12389 ⟨52, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (20572331763203 / 25000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (8952562229 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_53 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (82255509802421 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (1145929974873 / 50000000000000 : ℝ))
      (E := (cell12389 ⟨53, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (82255509802421 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (1145929974873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_54 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (41110857973953 / 50000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (229186391579 / 10000000000000 : ℝ))
      (E := (cell12389 ⟨54, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (41110857973953 / 50000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (229186391579 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_55 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (8218794546109 / 10000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (1145933971979 / 50000000000000 : ℝ))
      (E := (cell12389 ⟨55, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (8218794546109 / 10000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (1145933971979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_56 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (82154198313941 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291871913053 / 100000000000000 : ℝ))
      (E := (cell12389 ⟨56, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (82154198313941 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291871913053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_57 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (16424094895713 / 20000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (45837518759 / 2000000000000 : ℝ))
      (E := (cell12389 ⟨57, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (16424094895713 / 20000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (45837518759 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_58 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (82086773927209 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291879956081 / 100000000000000 : ℝ))
      (E := (cell12389 ⟨58, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (82086773927209 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291879956081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_59 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (1282079634879 / 1562500000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (1145941981871 / 50000000000000 : ℝ))
      (E := (cell12389 ⟨59, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (1282079634879 / 1562500000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (1145941981871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12390_40 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (82696966433097 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (229167093117 / 10000000000000 : ℝ))
      (E := (cell12390 ⟨40, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (82696966433097 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (229167093117 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_41 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (41331433248279 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291674943383 / 100000000000000 : ℝ))
      (E := (cell12390 ⟨41, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (41331433248279 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291674943383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_42 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (82628790304857 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145839460737 / 50000000000000 : ℝ))
      (E := (cell12390 ⟨42, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (82628790304857 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145839460737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_43 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (2581085557127 / 3125000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291682923869 / 100000000000000 : ℝ))
      (E := (cell12390 ⟨43, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (2581085557127 / 3125000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291682923869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_44 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (41280354518199 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291686891249 / 100000000000000 : ℝ))
      (E := (cell12390 ⟨44, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (41280354518199 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291686891249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_45 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (20631675975057 / 25000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145845470243 / 50000000000000 : ℝ))
      (E := (cell12390 ⟨45, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (20631675975057 / 25000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145845470243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_46 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (82492722390073 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (572923723533 / 25000000000000 : ℝ))
      (E := (cell12390 ⟨46, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (82492722390073 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (572923723533 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_47 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (82458764476603 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (572924731881 / 25000000000000 : ℝ))
      (E := (cell12390 ⟨47, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (82458764476603 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (572924731881 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_48 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (10303103766329 / 12500000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291702921547 / 100000000000000 : ℝ))
      (E := (cell12390 ⟨48, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (10303103766329 / 12500000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291702921547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_49 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (82390919323123 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (458341386693 / 20000000000000 : ℝ))
      (E := (cell12390 ⟨49, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (82390919323123 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (458341386693 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_50 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (16471406405037 / 20000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (458342180503 / 20000000000000 : ℝ))
      (E := (cell12390 ⟨50, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (16471406405037 / 20000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (458342180503 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_51 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (82323168208071 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291714885581 / 100000000000000 : ℝ))
      (E := (cell12390 ⟨51, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (82323168208071 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291714885581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_52 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (82289327843181 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (91668757577 / 4000000000000 : ℝ))
      (E := (cell12390 ⟨52, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (82289327843181 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (91668757577 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_53 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (41127755451027 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291722884603 / 100000000000000 : ℝ))
      (E := (cell12390 ⟨53, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (41127755451027 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291722884603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_54 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (10277714669547 / 12500000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (572931723863 / 25000000000000 : ℝ))
      (E := (cell12390 ⟨54, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (10277714669547 / 12500000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (572931723863 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_55 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (41093973588987 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145865455051 / 50000000000000 : ℝ))
      (E := (cell12390 ⟨55, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (41093973588987 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145865455051 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_56 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (82154200338813 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145867462737 / 50000000000000 : ℝ))
      (E := (cell12390 ⟨56, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (82154200338813 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145867462737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_57 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (41060238405501 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145869469139 / 50000000000000 : ℝ))
      (E := (cell12390 ⟨57, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (41060238405501 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145869469139 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_58 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (20521694141697 / 25000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (18333943087 / 800000000000 : ℝ))
      (E := (cell12390 ⟨58, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (20521694141697 / 25000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (18333943087 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_59 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (16410619915711 / 20000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291746882817 / 100000000000000 : ℝ))
      (E := (cell12390 ⟨59, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (16410619915711 / 20000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291746882817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12391_40 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (10337120434971 / 12500000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291533935699 / 100000000000000 : ℝ))
      (E := (cell12391 ⟨40, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (10337120434971 / 12500000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291533935699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_41 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (82662863857623 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (572884495799 / 25000000000000 : ℝ))
      (E := (cell12391 ⟨41, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (82662863857623 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (572884495799 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_42 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (82628787979881 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (572885484641 / 25000000000000 : ℝ))
      (E := (cell12391 ⟨42, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (82628787979881 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (572885484641 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_43 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (82594735816613 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (1145772988867 / 50000000000000 : ℝ))
      (E := (cell12391 ⟨43, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (82594735816613 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (1145772988867 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_44 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (41280353669019 / 50000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (572887480959 / 25000000000000 : ℝ))
      (E := (cell12391 ⟨44, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (41280353669019 / 50000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (572887480959 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_45 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (41263351257263 / 50000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (1145776976251 / 50000000000000 : ℝ))
      (E := (cell12391 ⟨45, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (41263351257263 / 50000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (1145776976251 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_46 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (82492721316599 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291557945141 / 100000000000000 : ℝ))
      (E := (cell12391 ⟨46, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (82492721316599 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291557945141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_47 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (20614690928731 / 25000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (1145780979701 / 50000000000000 : ℝ))
      (E := (cell12391 ⟨47, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (20614690928731 / 25000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (1145780979701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_48 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (82424829680319 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291565934999 / 100000000000000 : ℝ))
      (E := (cell12391 ⟨48, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (82424829680319 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291565934999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_49 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (41195459591873 / 50000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (572892482299 / 25000000000000 : ℝ))
      (E := (cell12391 ⟨49, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (41195459591873 / 50000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (572892482299 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_50 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (16471406439263 / 20000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291573940183 / 100000000000000 : ℝ))
      (E := (cell12391 ⟨50, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (16471406439263 / 20000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291573940183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_51 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (82323168689281 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291577965937 / 100000000000000 : ℝ))
      (E := (cell12391 ⟨51, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (82323168689281 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291577965937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_52 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (41144664317021 / 50000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (1145790972611 / 50000000000000 : ℝ))
      (E := (cell12391 ⟨52, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (41144664317021 / 50000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (1145790972611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_53 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (82255512002141 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291585934541 / 100000000000000 : ℝ))
      (E := (cell12391 ⟨53, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (82255512002141 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291585934541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_54 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (82221718765263 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (1145794965617 / 50000000000000 : ℝ))
      (E := (cell12391 ⟨54, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (82221718765263 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (1145794965617 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_55 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (16437589779047 / 20000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (229159393243 / 10000000000000 : ℝ))
      (E := (cell12391 ⟨55, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (16437589779047 / 20000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (229159393243 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_56 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (3286168094561 / 4000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291597935047 / 100000000000000 : ℝ))
      (E := (cell12391 ⟨56, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (3286168094561 / 4000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291597935047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_57 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (4106023957187 / 5000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (1145800967899 / 50000000000000 : ℝ))
      (E := (cell12391 ⟨57, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (4106023957187 / 5000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (1145800967899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_58 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (8208677920663 / 10000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (114580296559 / 5000000000000 : ℝ))
      (E := (cell12391 ⟨58, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (8208677920663 / 10000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (114580296559 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_59 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (82053102525079 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (229160991749 / 10000000000000 : ℝ))
      (E := (cell12391 ⟨59, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (82053102525079 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (229160991749 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12392_40 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (82696960527397 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (114569852709 / 5000000000000 : ℝ))
      (E := (cell12392 ⟨40, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (82696960527397 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (114569852709 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_41 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (41331430609803 / 50000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (572850269577 / 25000000000000 : ℝ))
      (E := (cell12392 ⟨41, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (41331430609803 / 50000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (572850269577 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_42 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (16525757131157 / 20000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291405069781 / 100000000000000 : ℝ))
      (E := (cell12392 ⟨42, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (16525757131157 / 20000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291405069781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_43 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (41297366903001 / 50000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291409028239 / 100000000000000 : ℝ))
      (E := (cell12392 ⟨43, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (41297366903001 / 50000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291409028239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_44 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (82560705640479 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291413070723 / 100000000000000 : ℝ))
      (E := (cell12392 ⟨44, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (82560705640479 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291413070723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_45 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (20631675282397 / 25000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (229141702007 / 10000000000000 : ℝ))
      (E := (cell12392 ⟨45, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (20631675282397 / 25000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (229141702007 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_46 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (10311590030481 / 12500000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291421051769 / 100000000000000 : ℝ))
      (E := (cell12392 ⟨46, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (10311590030481 / 12500000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291421051769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_47 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (82458762953931 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (28642813087 / 1250000000000 : ℝ))
      (E := (cell12392 ⟨47, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (82458762953931 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (28642813087 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_48 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (20606207307663 / 25000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291429063099 / 100000000000000 : ℝ))
      (E := (cell12392 ⟨48, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (20606207307663 / 25000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291429063099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_49 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (82390919044977 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (1145716519831 / 50000000000000 : ℝ))
      (E := (cell12392 ⟨49, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (82390919044977 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (1145716519831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_50 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (16471406473603 / 20000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (57285925843 / 2500000000000 : ℝ))
      (E := (cell12392 ⟨50, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (16471406473603 / 20000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (57285925843 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_51 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (82323169171021 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (9165764173 / 400000000000 : ℝ))
      (E := (cell12392 ⟨51, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (82323169171021 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (9165764173 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_52 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (20572332356349 / 25000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (572861266503 / 25000000000000 : ℝ))
      (E := (cell12392 ⟨52, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (20572332356349 / 25000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (572861266503 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_53 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (41127756551341 / 50000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (286431130067 / 12500000000000 : ℝ))
      (E := (cell12392 ⟨53, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (41127756551341 / 50000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (286431130067 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_54 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (16444344034913 / 20000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (71607906973 / 3125000000000 : ℝ))
      (E := (cell12392 ⟨54, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (16444344034913 / 20000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (71607906973 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_55 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (41093975306437 / 50000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (229145707001 / 10000000000000 : ℝ))
      (E := (cell12392 ⟨55, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (41093975306437 / 50000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (229145707001 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_56 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (3286168175583 / 4000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291461059961 / 100000000000000 : ℝ))
      (E := (cell12392 ⟨56, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (3286168175583 / 4000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291461059961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_57 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (4106024073839 / 5000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291465048743 / 100000000000000 : ℝ))
      (E := (cell12392 ⟨57, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (4106024073839 / 5000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291465048743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_58 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (16417356369347 / 20000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (1145734516429 / 50000000000000 : ℝ))
      (E := (cell12392 ⟨58, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (16417356369347 / 20000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (1145734516429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_59 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (82053105471827 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291473067763 / 100000000000000 : ℝ))
      (E := (cell12392 ⟨59, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (82053105471827 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291473067763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12393_40 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (82696957575983 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (1145630113949 / 50000000000000 : ℝ))
      (E := (cell12393 ⟨40, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (82696957575983 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (1145630113949 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_41 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (20665714645627 / 25000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291264228719 / 100000000000000 : ℝ))
      (E := (cell12393 ⟨41, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (20665714645627 / 25000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291264228719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_42 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (82628783332567 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (1145634098799 / 50000000000000 : ℝ))
      (E := (cell12393 ⟨42, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (82628783332567 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (1145634098799 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_43 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (82594731796231 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (1145636096479 / 50000000000000 : ℝ))
      (E := (cell12393 ⟨43, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (82594731796231 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (1145636096479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_44 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (41280351971861 / 50000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291276214289 / 100000000000000 : ℝ))
      (E := (cell12393 ⟨44, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (41280351971861 / 50000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291276214289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_45 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (82526699745411 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291280202027 / 100000000000000 : ℝ))
      (E := (cell12393 ⟨45, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (82526699745411 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291280202027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_46 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (82492719171821 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (572821053503 / 25000000000000 : ℝ))
      (E := (cell12393 ⟨46, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (82492719171821 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (572821053503 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_47 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (41229381096811 / 50000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (1145644095099 / 50000000000000 : ℝ))
      (E := (cell12393 ⟨47, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (41229381096811 / 50000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (1145644095099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_48 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (1287887949713 / 1562500000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291292188037 / 100000000000000 : ℝ))
      (E := (cell12393 ⟨48, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (1287887949713 / 1562500000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291292188037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_49 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (16478183781363 / 20000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (458259241187 / 20000000000000 : ℝ))
      (E := (cell12393 ⟨49, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (16478183781363 / 20000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (458259241187 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_50 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (82357032540283 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (286412522891 / 12500000000000 : ℝ))
      (E := (cell12393 ⟨50, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (82357032540283 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (286412522891 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_51 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (20580792413323 / 25000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (458260835299 / 20000000000000 : ℝ))
      (E := (cell12393 ⟨51, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (20580792413323 / 25000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (458260835299 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_52 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (41144665108621 / 50000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291308183799 / 100000000000000 : ℝ))
      (E := (cell12393 ⟨52, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (41144665108621 / 50000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291308183799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_53 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (82255514203677 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (229131220259 / 10000000000000 : ℝ))
      (E := (cell12393 ⟨53, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (82255514203677 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (229131220259 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_54 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (82221721584283 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (1145658115103 / 50000000000000 : ℝ))
      (E := (cell12393 ⟨54, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (82221721584283 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (1145658115103 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_55 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (82187952330889 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (1145660102353 / 50000000000000 : ℝ))
      (E := (cell12393 ⟨55, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (82187952330889 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (1145660102353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_56 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (16430841283093 / 20000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (572831045507 / 25000000000000 : ℝ))
      (E := (cell12393 ⟨56, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (16430841283093 / 20000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (572831045507 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_57 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (2053012095253 / 2500000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (1145664108999 / 50000000000000 : ℝ))
      (E := (cell12393 ⟨57, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (2053012095253 / 2500000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (1145664108999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_58 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (41043392243551 / 50000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (572833047727 / 25000000000000 : ℝ))
      (E := (cell12393 ⟨58, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (41043392243551 / 50000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (572833047727 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_59 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (205132771047 / 250000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (458267243061 / 20000000000000 : ℝ))
      (E := (cell12393 ⟨59, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (205132771047 / 250000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (458267243061 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12394_40 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (3307878185021 / 4000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145561728427 / 50000000000000 : ℝ))
      (E := (cell12394 ⟨40, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (3307878185021 / 4000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145561728427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_41 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (82662855946327 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291127434433 / 100000000000000 : ℝ))
      (E := (cell12394 ⟨41, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (82662855946327 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291127434433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_42 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (20657195252557 / 25000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291131439543 / 100000000000000 : ℝ))
      (E := (cell12394 ⟨42, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (20657195252557 / 25000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291131439543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_43 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (825947297873 / 1000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (458227082621 / 20000000000000 : ℝ))
      (E := (cell12394 ⟨43, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (825947297873 / 1000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (458227082621 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_44 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (16512140449553 / 20000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291139413347 / 100000000000000 : ℝ))
      (E := (cell12394 ⟨44, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (16512140449553 / 20000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291139413347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_45 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (82526698361997 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291143439539 / 100000000000000 : ℝ))
      (E := (cell12394 ⟨45, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (82526698361997 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291143439539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_46 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (82492718100517 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (3665835891 / 160000000000 : ℝ))
      (E := (cell12394 ⟨46, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (82492718100517 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (3665835891 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_47 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (41229380716999 / 50000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291151447999 / 100000000000000 : ℝ))
      (E := (cell12394 ⟨47, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (41229380716999 / 50000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291151447999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_48 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (82424828333257 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145577713813 / 50000000000000 : ℝ))
      (E := (cell12394 ⟨48, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (82424828333257 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145577713813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_49 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (82390918769261 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (143197464251 / 6250000000000 : ℝ))
      (E := (cell12394 ⟨49, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (82390918769261 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (143197464251 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_50 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (82357032713121 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145581723679 / 50000000000000 : ℝ))
      (E := (cell12394 ⟨50, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (82357032713121 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145581723679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_51 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (82323170136093 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (45823348493 / 2000000000000 : ℝ))
      (E := (cell12394 ⟨51, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (82323170136093 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (45823348493 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_52 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (4114466550479 / 5000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145585708291 / 50000000000000 : ℝ))
      (E := (cell12394 ⟨52, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (4114466550479 / 5000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145585708291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_53 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (658044122441 / 800000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (71599231897 / 3125000000000 : ℝ))
      (E := (cell12394 ⟨53, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (658044122441 / 800000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (71599231897 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_54 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (5138857687151 / 6250000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291179434353 / 100000000000000 : ℝ))
      (E := (cell12394 ⟨54, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (5138857687151 / 6250000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291179434353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_55 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (41093977024641 / 50000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145591697793 / 50000000000000 : ℝ))
      (E := (cell12394 ⟨55, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (41093977024641 / 50000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145591697793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_56 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (41077104220847 / 50000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (572796854859 / 25000000000000 : ℝ))
      (E := (cell12394 ⟨56, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (41077104220847 / 50000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (572796854859 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_57 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (1026506076797 / 1250000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (458238288713 / 20000000000000 : ℝ))
      (E := (cell12394 ⟨57, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (1026506076797 / 1250000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (458238288713 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_58 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (20521696781933 / 25000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291195405331 / 100000000000000 : ℝ))
      (E := (cell12394 ⟨58, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (20521696781933 / 25000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291195405331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_59 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (41026555682999 / 50000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (572799854821 / 25000000000000 : ℝ))
      (E := (cell12394 ⟨59, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (41026555682999 / 50000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (572799854821 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12395_40 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (10337118959503 / 12500000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (286373342631 / 12500000000000 : ℝ))
      (E := (cell12395 ⟨40, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (10337118959503 / 12500000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (286373342631 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_41 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (82662853311063 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290990695449 / 100000000000000 : ℝ))
      (E := (cell12395 ⟨41, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (82662853311063 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290990695449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_42 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (82628778688767 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (458198947371 / 20000000000000 : ℝ))
      (E := (cell12395 ⟨42, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (82628778688767 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (458198947371 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_43 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (10324340972401 / 12500000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (1145499344341 / 50000000000000 : ℝ))
      (E := (cell12395 ⟨43, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (10324340972401 / 12500000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (1145499344341 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_44 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (82560700552609 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2291002726709 / 100000000000000 : ℝ))
      (E := (cell12395 ⟨44, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (82560700552609 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2291002726709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_45 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (5157918561209 / 6250000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2291006732607 / 100000000000000 : ℝ))
      (E := (cell12395 ⟨45, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (5157918561209 / 6250000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2291006732607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_46 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (82492717029937 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (572752676339 / 25000000000000 : ℝ))
      (E := (cell12395 ⟨46, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (82492717029937 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (572752676339 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_47 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (41229380337529 / 50000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (1145507351301 / 50000000000000 : ℝ))
      (E := (cell12395 ⟨47, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (41229380337529 / 50000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (1145507351301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_48 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (10303103485691 / 12500000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (28637734037 / 1250000000000 : ℝ))
      (E := (cell12395 ⟨48, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (10303103485691 / 12500000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (28637734037 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_49 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (41195459316157 / 50000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (1145511352953 / 50000000000000 : ℝ))
      (E := (cell12395 ⟨49, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (41195459316157 / 50000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (1145511352953 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_50 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (82357032886527 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2291026708507 / 100000000000000 : ℝ))
      (E := (cell12395 ⟨50, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (82357032886527 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2291026708507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_51 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (2572599081857 / 3125000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (114551536437 / 5000000000000 : ℝ))
      (E := (cell12395 ⟨51, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (2572599081857 / 3125000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (114551536437 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_52 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (82289331802409 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (572758676341 / 25000000000000 : ℝ))
      (E := (cell12395 ⟨52, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (82289331802409 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (572758676341 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_53 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (82255516407027 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (1145519347439 / 50000000000000 : ℝ))
      (E := (cell12395 ⟨53, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (82255516407027 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (1145519347439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_54 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (20555431101241 / 25000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2291042694623 / 100000000000000 : ℝ))
      (E := (cell12395 ⟨54, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (20555431101241 / 25000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2291042694623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_55 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (20546988942013 / 25000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (1145523350861 / 50000000000000 : ℝ))
      (E := (cell12395 ⟨55, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (20546988942013 / 25000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (1145523350861 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_56 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (82154210468261 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2291050713093 / 100000000000000 : ℝ))
      (E := (cell12395 ⟨56, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (82154210468261 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2291050713093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_57 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (41060244238851 / 50000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (1145527362721 / 50000000000000 : ℝ))
      (E := (cell12395 ⟨57, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (41060244238851 / 50000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (1145527362721 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_58 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (656694318149 / 800000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2291058676129 / 100000000000000 : ℝ))
      (E := (cell12395 ⟨58, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (656694318149 / 800000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2291058676129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_59 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (4102655715671 / 5000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (22910626797 / 1000000000000 : ℝ))
      (E := (cell12395 ⟨59, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (4102655715671 / 5000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (22910626797 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12396_40 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (82696948727479 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (572712520121 / 25000000000000 : ℝ))
      (E := (cell12396 ⟨40, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (82696948727479 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (572712520121 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_41 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (82662850676717 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290854070509 / 100000000000000 : ℝ))
      (E := (cell12396 ⟨41, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (82662850676717 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290854070509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_42 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (16525755273637 / 20000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (229085803077 / 10000000000000 : ℝ))
      (E := (cell12396 ⟨42, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (16525755273637 / 20000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (229085803077 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_43 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (16518945154391 / 20000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (1145431039239 / 50000000000000 : ℝ))
      (E := (cell12396 ⟨43, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (16518945154391 / 20000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (1145431039239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_44 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (82560698858253 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (458173207351 / 20000000000000 : ℝ))
      (E := (cell12396 ⟨44, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (82560698858253 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (458173207351 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_45 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (82526695597453 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290870022399 / 100000000000000 : ℝ))
      (E := (cell12396 ⟨45, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (82526695597453 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290870022399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_46 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (82492715960079 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290874034459 / 100000000000000 : ℝ))
      (E := (cell12396 ⟨46, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (82492715960079 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290874034459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_47 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (82458759916803 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (229087807177 / 10000000000000 : ℝ))
      (E := (cell12396 ⟨47, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (82458759916803 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (229087807177 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_48 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (16484965487689 / 20000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (1145441037021 / 50000000000000 : ℝ))
      (E := (cell12396 ⟨48, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (16484965487689 / 20000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (1145441037021 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_49 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (82390918495973 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290886039607 / 100000000000000 : ℝ))
      (E := (cell12396 ⟨49, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (82390918495973 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290886039607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_50 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (82357033060501 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (572722506383 / 25000000000000 : ℝ))
      (E := (cell12396 ⟨50, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (82357033060501 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (572722506383 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_51 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (41161585551643 / 50000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290894029791 / 100000000000000 : ℝ))
      (E := (cell12396 ⟨51, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (41161585551643 / 50000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290894029791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_52 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (8228933259573 / 10000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (458179610029 / 20000000000000 : ℝ))
      (E := (cell12396 ⟨52, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (8228933259573 / 10000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (458179610029 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_53 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (82255517509381 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290902025117 / 100000000000000 : ℝ))
      (E := (cell12396 ⟨53, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (82255517509381 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290902025117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_54 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (82221725815927 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (1145453035033 / 50000000000000 : ℝ))
      (E := (cell12396 ⟨54, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (82221725815927 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (1145453035033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_55 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (41093978743599 / 50000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (143181879003 / 6250000000000 : ℝ))
      (E := (cell12396 ⟨55, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (41093978743599 / 50000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (143181879003 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_56 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (41077106247583 / 50000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290914063003 / 100000000000000 : ℝ))
      (E := (cell12396 ⟨56, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (41077106247583 / 50000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290914063003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_57 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (82120490811943 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (458183612727 / 20000000000000 : ℝ))
      (E := (cell12396 ⟨57, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (82120490811943 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (458183612727 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_58 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (4104339620489 / 5000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (572730515611 / 25000000000000 : ℝ))
      (E := (cell12396 ⟨58, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (4104339620489 / 5000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (572730515611 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_59 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (82053117261067 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (1145463027859 / 50000000000000 : ℝ))
      (E := (cell12396 ⟨59, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (82053117261067 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (1145463027859 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12397_40 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (8269694577989 / 10000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290713475161 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨40, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (8269694577989 / 10000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290713475161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_41 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (82662848043287 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (458143488427 / 20000000000000 : ℝ))
      (E := (cell12397 ⟨41, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (82662848043287 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (458143488427 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_42 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (516429837803 / 625000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290721438819 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨42, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (516429837803 / 625000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290721438819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_43 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (41297361882771 / 50000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (1145362732459 / 50000000000000 : ℝ))
      (E := (cell12397 ⟨43, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (41297361882771 / 50000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (1145362732459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_44 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (41280348582349 / 50000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (572682365277 / 25000000000000 : ℝ))
      (E := (cell12397 ⟨44, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (41280348582349 / 50000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (572682365277 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_45 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (20631673554081 / 25000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (286341678323 / 12500000000000 : ℝ))
      (E := (cell12397 ⟨45, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (20631673554081 / 25000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (286341678323 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_46 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (82492714890943 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (572684369511 / 25000000000000 : ℝ))
      (E := (cell12397 ⟨46, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (82492714890943 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (572684369511 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_47 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (82458759159231 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290741437743 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨47, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (82458759159231 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290741437743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_48 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (82424826992007 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (143171588873 / 6250000000000 : ℝ))
      (E := (cell12397 ⟨48, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (82424826992007 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (143171588873 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_49 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (1029886479503 / 1250000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290749429119 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨49, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (1029886479503 / 1250000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290749429119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_50 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (82357033235043 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (286344182173 / 12500000000000 : ℝ))
      (E := (cell12397 ⟨50, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (82357033235043 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (286344182173 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_51 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (82323171587677 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (572689361439 / 25000000000000 : ℝ))
      (E := (cell12397 ⟨51, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (82323171587677 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (572689361439 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_52 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (82289333389543 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290761450927 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨52, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (82289333389543 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290761450927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_53 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (82255518612189 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290765470441 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨53, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (82255518612189 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290765470441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_54 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (16444345445461 / 20000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (572692360647 / 25000000000000 : ℝ))
      (E := (cell12397 ⟨54, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (16444345445461 / 20000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (572692360647 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_55 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (82187959206721 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290773423493 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨55, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (82187959206721 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290773423493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_56 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (8215421452241 / 10000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290777469163 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨56, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (8215421452241 / 10000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290777469163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_57 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (16424098629297 / 20000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290781458141 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨57, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (16424098629297 / 20000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290781458141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_58 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (82086795051197 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (458157089199 / 20000000000000 : ℝ))
      (E := (cell12397 ⟨58, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (82086795051197 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (458157089199 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_59 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (82053120208937 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290789429013 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨59, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (82053120208937 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290789429013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12398_40 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (82696942833257 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (57264423127 / 2500000000000 : ℝ))
      (E := (cell12398 ⟨40, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (82696942833257 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (57264423127 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_41 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (41331422705387 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (35790326997 / 1562500000000 : ℝ))
      (E := (cell12398 ⟨41, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (41331422705387 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (35790326997 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_42 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (82628771729653 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290584902237 / 100000000000000 : ℝ))
      (E := (cell12398 ⟨42, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (82628771729653 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290584902237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_43 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (82594721759967 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (286323613349 / 12500000000000 : ℝ))
      (E := (cell12398 ⟨43, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (82594721759967 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (286323613349 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_44 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (41280347735971 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290592940957 / 100000000000000 : ℝ))
      (E := (cell12398 ⟨44, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (41280347735971 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290592940957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_45 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (16505338567191 / 20000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (572649236291 / 25000000000000 : ℝ))
      (E := (cell12398 ⟨45, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (16505338567191 / 20000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (572649236291 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_46 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (8249271382253 / 10000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (286325114799 / 12500000000000 : ℝ))
      (E := (cell12398 ⟨46, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (8249271382253 / 10000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (286325114799 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_47 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (82458758402343 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290604918283 / 100000000000000 : ℝ))
      (E := (cell12398 ⟨47, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (82458758402343 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290604918283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_48 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (41212413273107 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290608943453 / 100000000000000 : ℝ))
      (E := (cell12398 ⟨48, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (41212413273107 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290608943453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_49 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (82390918225113 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290612933373 / 100000000000000 : ℝ))
      (E := (cell12398 ⟨49, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (82390918225113 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290612933373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_50 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (41178516705077 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (1145308443079 / 50000000000000 : ℝ))
      (E := (cell12398 ⟨50, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (41178516705077 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (1145308443079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_51 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (82323172072597 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (114531045883 / 5000000000000 : ℝ))
      (E := (cell12398 ⟨51, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (82323172072597 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (114531045883 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_52 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (82289334183847 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (229062490771 / 10000000000000 : ℝ))
      (E := (cell12398 ⟨52, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (82289334183847 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (229062490771 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_53 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (1645110394309 / 2000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (1145314456403 / 50000000000000 : ℝ))
      (E := (cell12398 ⟨53, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (1645110394309 / 2000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (1145314456403 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_54 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (82221728639097 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (572658232571 / 25000000000000 : ℝ))
      (E := (cell12398 ⟨54, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (82221728639097 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (572658232571 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_55 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (4109398046331 / 5000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290636898197 / 100000000000000 : ℝ))
      (E := (cell12398 ⟨55, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (4109398046331 / 5000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290636898197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_56 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (10269277068749 / 12500000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290640931577 / 100000000000000 : ℝ))
      (E := (cell12398 ⟨56, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (10269277068749 / 12500000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290640931577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_57 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (82120495481327 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290644908963 / 100000000000000 : ℝ))
      (E := (cell12398 ⟨57, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (82120495481327 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290644908963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_58 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (20521699423219 / 25000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (572662221481 / 25000000000000 : ℝ))
      (E := (cell12398 ⟨58, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (20521699423219 / 25000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (572662221481 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_59 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (10256640394629 / 12500000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290652917911 / 100000000000000 : ℝ))
      (E := (cell12398 ⟨59, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (10256640394629 / 12500000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290652917911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12399_40 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (82696939887579 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (572610107561 / 25000000000000 : ℝ))
      (E := (cell12399 ⟨40, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (82696939887579 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (572610107561 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_41 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (41331421389589 / 50000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290444468787 / 100000000000000 : ℝ))
      (E := (cell12399 ⟨41, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (41331421389589 / 50000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290444468787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_42 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (82628769411703 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (1145224210513 / 50000000000000 : ℝ))
      (E := (cell12399 ⟨42, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (82628769411703 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (1145224210513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_43 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (82594719755231 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290452462887 / 100000000000000 : ℝ))
      (E := (cell12399 ⟨43, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (82594719755231 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290452462887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_44 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (41280346889993 / 50000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290456417493 / 100000000000000 : ℝ))
      (E := (cell12399 ⟨44, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (41280346889993 / 50000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290456417493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_45 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (82526691456347 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290460460471 / 100000000000000 : ℝ))
      (E := (cell12399 ⟨45, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (82526691456347 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290460460471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_46 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (82492712754839 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (458092882873 / 20000000000000 : ℝ))
      (E := (cell12399 ⟨46, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (82492712754839 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (458092882873 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_47 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (41229378823069 / 50000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (143154278407 / 6250000000000 : ℝ))
      (E := (cell12399 ⟨47, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (41229378823069 / 50000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (143154278407 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_48 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (41212413050533 / 50000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (286309057723 / 12500000000000 : ℝ))
      (E := (cell12399 ⟨48, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (41212413050533 / 50000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (286309057723 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_49 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (2574716190331 / 3125000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (143154777157 / 6250000000000 : ℝ))
      (E := (cell12399 ⟨49, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (2574716190331 / 3125000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (143154777157 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_50 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (10294629198229 / 12500000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (1145240214881 / 50000000000000 : ℝ))
      (E := (cell12399 ⟨50, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (10294629198229 / 12500000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (1145240214881 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_51 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (82323172558047 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (35788819461 / 1562500000000 : ℝ))
      (E := (cell12399 ⟨51, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (82323172558047 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (35788819461 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_52 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (82289334978641 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (143155526281 / 6250000000000 : ℝ))
      (E := (cell12399 ⟨52, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (82289334978641 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (143155526281 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_53 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (82255520819163 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290492411237 / 100000000000000 : ℝ))
      (E := (cell12399 ⟨53, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (82255520819163 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290492411237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_54 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (82221730051303 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (1145248207531 / 50000000000000 : ℝ))
      (E := (cell12399 ⟨54, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (82221730051303 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (1145248207531 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_55 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (16437592529379 / 20000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290500429093 / 100000000000000 : ℝ))
      (E := (cell12399 ⟨55, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (16437592529379 / 20000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290500429093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_56 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (10269277322239 / 12500000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (572626112561 / 25000000000000 : ℝ))
      (E := (cell12399 ⟨56, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (10269277322239 / 12500000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (572626112561 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_57 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (82120497816469 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290508416101 / 100000000000000 : ℝ))
      (E := (cell12399 ⟨57, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (82120497816469 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290508416101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_58 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (82086800334817 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290512441373 / 100000000000000 : ℝ))
      (E := (cell12399 ⟨58, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (82086800334817 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290512441373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_59 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (1641062522107 / 2000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290516463253 / 100000000000000 : ℝ))
      (E := (cell12399 ⟨59, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (1641062522107 / 2000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290516463253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

end BstLean.Part268
