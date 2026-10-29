import BstLean.Part268CellShard34Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert13200_20 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (10421952821269 / 12500000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193671187653 / 100000000000000 : ℝ))
      (E := (cell13200 ⟨20, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (10421952821269 / 12500000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193671187653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_21 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (1041765299277 / 1250000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096837577697 / 50000000000000 : ℝ))
      (E := (cell13200 ⟨21, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (1041765299277 / 1250000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096837577697 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_22 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (83306849436753 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193679190279 / 100000000000000 : ℝ))
      (E := (cell13200 ⟨22, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (83306849436753 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193679190279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_23 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (16654499804257 / 20000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096841618647 / 50000000000000 : ℝ))
      (E := (cell13200 ⟨23, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (16654499804257 / 20000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096841618647 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_24 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (20809543165819 / 25000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096843620547 / 50000000000000 : ℝ))
      (E := (cell13200 ⟨24, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (20809543165819 / 25000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096843620547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_25 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (20800967582603 / 25000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193691262897 / 100000000000000 : ℝ))
      (E := (cell13200 ⟨25, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (20800967582603 / 25000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193691262897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_26 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (83169591990547 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (548423811711 / 25000000000000 : ℝ))
      (E := (cell13200 ⟨26, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (83169591990547 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (548423811711 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_27 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (5195958600731 / 6250000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096849626867 / 50000000000000 : ℝ))
      (E := (cell13200 ⟨27, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (5195958600731 / 6250000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096849626867 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_28 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (2077527679051 / 2500000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193703285711 / 100000000000000 : ℝ))
      (E := (cell13200 ⟨28, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (2077527679051 / 2500000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193703285711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_29 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (83066900609921 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193707344693 / 100000000000000 : ℝ))
      (E := (cell13200 ⟨29, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (83066900609921 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193707344693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_30 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (83032717923843 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (137106957203 / 6250000000000 : ℝ))
      (E := (cell13200 ⟨30, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (83032717923843 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (137106957203 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_31 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (8299855907247 / 10000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193715374443 / 100000000000000 : ℝ))
      (E := (cell13200 ⟨31, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (8299855907247 / 10000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193715374443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_32 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (663715392197 / 800000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (27421491847 / 1250000000000 : ℝ))
      (E := (cell13200 ⟨32, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (663715392197 / 800000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (27421491847 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_33 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (8293031274929 / 10000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (548430852989 / 25000000000000 : ℝ))
      (E := (cell13200 ⟨33, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (8293031274929 / 10000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (548430852989 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_34 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (41448112607803 / 50000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096863695959 / 50000000000000 : ℝ))
      (E := (cell13200 ⟨34, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (41448112607803 / 50000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096863695959 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_35 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (41431080696433 / 50000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193731405417 / 100000000000000 : ℝ))
      (E := (cell13200 ⟨35, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (41431080696433 / 50000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193731405417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_36 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (20707030312631 / 25000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (137108465799 / 6250000000000 : ℝ))
      (E := (cell13200 ⟨36, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (20707030312631 / 25000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (137108465799 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_37 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (10349263094773 / 12500000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (548434868851 / 25000000000000 : ℝ))
      (E := (cell13200 ⟨37, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (10349263094773 / 12500000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (548434868851 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_38 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (82760111885607 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096871736547 / 50000000000000 : ℝ))
      (E := (cell13200 ⟨38, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (82760111885607 / 100000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (1096871736547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13200_39 : CellCertificate 13200 (109153761732297 / 1250000000000000 : ℝ) (318244956218057 / 200000000000000000 : ℝ) (160566273053453 / 5000000000000000 : ℝ)
    (cell13200 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · norm_num [cell13200]
  · have h := gap_lower (n := 13200) (a := (16545228520541 / 20000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193747504221 / 100000000000000 : ℝ))
      (E := (cell13200 ⟨39, by decide⟩).energy) (xi := (160566273053453 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13200 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13200]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13200])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13200) (a := (16545228520541 / 20000000000000 : ℝ)) (b := (9748442021 / 6250000000000 : ℝ)) (q := (2193747504221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13200])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13200]

theorem cert13201_20 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (10421951086381 / 12500000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193561175161 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨20, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (10421951086381 / 12500000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193561175161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_21 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (20835302517291 / 25000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193565198969 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨21, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (20835302517291 / 25000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193565198969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_22 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (83306835569859 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (1096784615821 / 50000000000000 : ℝ))
      (E := (cell13201 ⟨22, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (83306835569859 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (1096784615821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_23 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (10409060645061 / 12500000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (438714643619 / 20000000000000 : ℝ))
      (E := (cell13201 ⟨23, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (10409060645061 / 12500000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (438714643619 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_24 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (8323815880857 / 10000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (1096788609877 / 50000000000000 : ℝ))
      (E := (cell13201 ⟨24, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (8323815880857 / 10000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (1096788609877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_25 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (83203856481793 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193581239461 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨25, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (83203856481793 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193581239461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_26 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (10396197268501 / 12500000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (1096792639913 / 50000000000000 : ℝ))
      (E := (cell13201 ⟨26, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (10396197268501 / 12500000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (1096792639913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_27 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (41567661887617 / 50000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (438717856947 / 20000000000000 : ℝ))
      (E := (cell13201 ⟨27, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (41567661887617 / 50000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (438717856947 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_28 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (1298454583307 / 1562500000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (109679665739 / 5000000000000 : ℝ))
      (E := (cell13201 ⟨28, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (1298454583307 / 1562500000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (109679665739 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_29 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (16613377357119 / 20000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193597313339 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨29, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (16613377357119 / 20000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193597313339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_30 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (41516352052789 / 50000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (219360134059 / 10000000000000 : ℝ))
      (E := (cell13201 ⟨30, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (41516352052789 / 50000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (219360134059 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_31 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (4149927263013 / 5000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (137100333713 / 6250000000000 : ℝ))
      (E := (cell13201 ⟨31, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (4149927263013 / 5000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (137100333713 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_32 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (41482205109233 / 50000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193609369561 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨32, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (41482205109233 / 50000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193609369561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_33 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (82930298949177 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (274201679007 / 12500000000000 : ℝ))
      (E := (cell13201 ⟨33, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (82930298949177 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (274201679007 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_34 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (82896211421533 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193617410363 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨34, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (82896211421533 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193617410363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_35 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (82862147604829 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (1096810711127 / 50000000000000 : ℝ))
      (E := (cell13201 ⟨35, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (82862147604829 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (1096810711127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_36 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (82828107468517 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193625468059 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨36, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (82828107468517 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193625468059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_37 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (41397045491101 / 50000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (548407372291 / 25000000000000 : ℝ))
      (E := (cell13201 ⟨37, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (41397045491101 / 50000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (548407372291 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_38 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (41380049057823 / 50000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193633485383 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨38, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (41380049057823 / 50000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193633485383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13201_39 : CellCertificate 13201 (174640830398583 / 2000000000000000 : ℝ) (1591104204761947 / 1000000000000000000 : ℝ) (160553833891093 / 5000000000000000 : ℝ)
    (cell13201 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · norm_num [cell13201]
  · have h := gap_lower (n := 13201) (a := (82726128838759 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193637515087 / 100000000000000 : ℝ))
      (E := (cell13201 ⟨39, by decide⟩).energy) (xi := (160553833891093 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13201 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13201]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13201])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13201) (a := (82726128838759 / 100000000000000 : ℝ)) (b := (155963122897 / 100000000000000 : ℝ)) (q := (2193637515087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13201])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13201]

theorem cert13202_20 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (1667511896281 / 2000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (1096725608419 / 50000000000000 : ℝ))
      (E := (cell13202 ⟨20, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (1667511896281 / 2000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (1096725608419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_21 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (83341196198271 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (219345523839 / 10000000000000 : ℝ))
      (E := (cell13202 ⟨21, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (83341196198271 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (219345523839 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_22 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (20826705426267 / 25000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193459268851 / 100000000000000 : ℝ))
      (E := (cell13202 ⟨22, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (20826705426267 / 25000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193459268851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_23 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (83272471301793 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193463253139 / 100000000000000 : ℝ))
      (E := (cell13202 ⟨23, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (83272471301793 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193463253139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_24 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (41619072477983 / 50000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (54836681317 / 2500000000000 : ℝ))
      (E := (cell13202 ⟨24, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (41619072477983 / 50000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (54836681317 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_25 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (41601921317637 / 50000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (438694254063 / 20000000000000 : ℝ))
      (E := (cell13202 ⟨25, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (41601921317637 / 50000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (438694254063 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_26 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (8316956430757 / 10000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (438695061731 / 20000000000000 : ℝ))
      (E := (cell13202 ⟨26, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (8316956430757 / 10000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (438695061731 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_27 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (8313530994087 / 10000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193479311587 / 100000000000000 : ℝ))
      (E := (cell13202 ⟨27, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (8313530994087 / 10000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193479311587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_28 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (16620215900671 / 20000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193483339699 / 100000000000000 : ℝ))
      (E := (cell13202 ⟨28, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (16620215900671 / 20000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193483339699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_29 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (83066872963367 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (548371834093 / 25000000000000 : ℝ))
      (E := (cell13202 ⟨29, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (83066872963367 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (548371834093 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_30 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (83032690289409 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (274186420223 / 12500000000000 : ℝ))
      (E := (cell13202 ⟨30, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (83032690289409 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (274186420223 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_31 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (41499265725073 / 50000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193495417393 / 100000000000000 : ℝ))
      (E := (cell13202 ⟨31, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (41499265725073 / 50000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193495417393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_32 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (82964396414401 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (34273428841 / 1562500000000 : ℝ))
      (E := (cell13202 ⟨32, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (82964396414401 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (34273428841 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_33 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (82930285151157 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193503448011 / 100000000000000 : ℝ))
      (E := (cell13202 ⟨33, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (82930285151157 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193503448011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_34 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (5181012351847 / 6250000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193507483319 / 100000000000000 : ℝ))
      (E := (cell13202 ⟨34, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (5181012351847 / 6250000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193507483319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_35 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (41431066909441 / 50000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (1096755746813 / 50000000000000 : ℝ))
      (E := (cell13202 ⟨35, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (41431066909441 / 50000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (1096755746813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_36 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (414140468443 / 500000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193515479191 / 100000000000000 : ℝ))
      (E := (cell13202 ⟨36, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (414140468443 / 500000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193515479191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_37 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (8279407720831 / 10000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193519498781 / 100000000000000 : ℝ))
      (E := (cell13202 ⟨37, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (8279407720831 / 10000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (2193519498781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_38 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (82760084347773 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (54838088807 / 2500000000000 : ℝ))
      (E := (cell13202 ⟨38, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (82760084347773 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (54838088807 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13202_39 : CellCertificate 13202 (873178213886563 / 10000000000000000 : ℝ) (795491823352879 / 500000000000000000 : ℝ) (321082793335153 / 10000000000000000 : ℝ)
    (cell13202 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · norm_num [cell13202]
  · have h := gap_lower (n := 13202) (a := (82726115076901 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (548381880453 / 25000000000000 : ℝ))
      (E := (cell13202 ⟨39, by decide⟩).energy) (xi := (321082793335153 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13202 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13202]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13202])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13202) (a := (82726115076901 / 100000000000000 : ℝ)) (b := (77975587647 / 50000000000000 : ℝ)) (q := (548381880453 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13202])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13202]

theorem cert13203_20 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (20843895234789 / 25000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193341254359 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨20, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (20843895234789 / 25000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193341254359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_21 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (83341182329483 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193345273653 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨21, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (83341182329483 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193345273653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_22 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (4165340392119 / 5000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (438669860381 / 20000000000000 : ℝ))
      (E := (cell13203 ⟨22, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (4165340392119 / 5000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (438669860381 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_23 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (208181143613 / 250000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193353284029 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨23, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (208181143613 / 250000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193353284029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_24 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (41619065552731 / 50000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193357339873 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨24, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (41619065552731 / 50000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193357339873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_25 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (16640765758171 / 20000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193361355461 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨25, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (16640765758171 / 20000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193361355461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_26 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (8316955046923 / 10000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (1096682666667 / 50000000000000 : ℝ))
      (E := (cell13203 ⟨26, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (8316955046923 / 10000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (1096682666667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_27 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (16627059221721 / 20000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193369392777 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨27, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (16627059221721 / 20000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193369392777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_28 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (83101065677159 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (1096686709491 / 50000000000000 : ℝ))
      (E := (cell13203 ⟨28, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (83101065677159 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (1096686709491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_29 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (16613371828647 / 20000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193377413793 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨29, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (16613371828647 / 20000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193377413793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_30 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (10379084559417 / 12500000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (219338143739 / 10000000000000 : ℝ))
      (E := (cell13203 ⟨30, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (10379084559417 / 12500000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (219338143739 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_31 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (41499258821063 / 50000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193385432647 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨31, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (41499258821063 / 50000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193385432647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_32 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (8296438261243 / 10000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (548347364833 / 25000000000000 : ℝ))
      (E := (cell13203 ⟨32, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (8296438261243 / 10000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (548347364833 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_33 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (8293027135523 / 10000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (43867870369 / 2000000000000 : ℝ))
      (E := (cell13203 ⟨33, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (8293027135523 / 10000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (43867870369 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_34 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (82896183839663 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (87735899739 / 4000000000000 : ℝ))
      (E := (cell13203 ⟨34, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (82896183839663 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (87735899739 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_35 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (82862120035027 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (87736060087 / 4000000000000 : ℝ))
      (E := (cell13203 ⟨35, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (82862120035027 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (87736060087 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_36 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (82828079910773 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193405544881 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨36, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (82828079910773 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193405544881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_37 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (82794063436507 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (109670478149 / 5000000000000 : ℝ))
      (E := (cell13203 ⟨37, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (82794063436507 / 100000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (109670478149 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_38 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (20690017645497 / 25000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193413556287 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨38, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (20690017645497 / 25000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193413556287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13203_39 : CellCertificate 13203 (27286008735577 / 312500000000000 : ℝ) (318172621383513 / 200000000000000000 : ℝ) (64211584552971 / 2000000000000000 : ℝ)
    (cell13203 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · norm_num [cell13203]
  · have h := gap_lower (n := 13203) (a := (8272610131713 / 10000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193417583169 / 100000000000000 : ℝ))
      (E := (cell13203 ⟨39, by decide⟩).energy) (xi := (64211584552971 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13203 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13203]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13203])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13203) (a := (8272610131713 / 10000000000000 : ℝ)) (b := (19492403691 / 12500000000000 : ℝ)) (q := (2193417583169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13203])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13203]

theorem cert13204_20 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (41687783533183 / 50000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193231346051 / 100000000000000 : ℝ))
      (E := (cell13204 ⟨20, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (41687783533183 / 50000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193231346051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_21 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (41670584231399 / 50000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (274154420389 / 12500000000000 : ℝ))
      (E := (cell13204 ⟨21, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (41670584231399 / 50000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (274154420389 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_22 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (41653396990897 / 50000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (1096619694589 / 50000000000000 : ℝ))
      (E := (cell13204 ⟨22, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (41653396990897 / 50000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (1096619694589 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_23 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (20818110897677 / 25000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193243369163 / 100000000000000 : ℝ))
      (E := (cell13204 ⟨23, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (20818110897677 / 25000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193243369163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_24 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (83238117257059 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (1096623711457 / 50000000000000 : ℝ))
      (E := (cell13204 ⟨24, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (83238117257059 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (1096623711457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_25 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (10400476868567 / 12500000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (438650287291 / 20000000000000 : ℝ))
      (E := (cell13204 ⟨25, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (10400476868567 / 12500000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (438650287291 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_26 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (8316953663299 / 10000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (274156926541 / 12500000000000 : ℝ))
      (E := (cell13204 ⟨26, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (8316953663299 / 10000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (274156926541 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_27 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (41567641139219 / 50000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (1096629734909 / 50000000000000 : ℝ))
      (E := (cell13204 ⟨27, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (41567641139219 / 50000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (1096629734909 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_28 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (4155052592653 / 5000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (548315873529 / 25000000000000 : ℝ))
      (E := (cell13204 ⟨28, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (4155052592653 / 5000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (548315873529 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_29 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (41533422662599 / 50000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (548316871767 / 25000000000000 : ℝ))
      (E := (cell13204 ⟨29, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (41533422662599 / 50000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (548316871767 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_30 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (83032662663357 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193271508851 / 100000000000000 : ℝ))
      (E := (cell13204 ⟨30, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (83032662663357 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193271508851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_31 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (82998503836201 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193275502339 / 100000000000000 : ℝ))
      (E := (cell13204 ⟨31, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (82998503836201 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193275502339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_32 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (82964368812553 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (1096639763651 / 50000000000000 : ℝ))
      (E := (cell13204 ⟨32, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (82964368812553 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (1096639763651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_33 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (41465128780697 / 50000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193283584747 / 100000000000000 : ℝ))
      (E := (cell13204 ⟨33, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (41465128780697 / 50000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193283584747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_34 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (41448085025933 / 50000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193287558141 / 100000000000000 : ℝ))
      (E := (cell13204 ⟨34, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (41448085025933 / 50000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193287558141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_35 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (41431053126631 / 50000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193291623937 / 100000000000000 : ℝ))
      (E := (cell13204 ⟨35, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (41431053126631 / 50000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193291623937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_36 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (20707016533759 / 25000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (219329560643 / 10000000000000 : ℝ))
      (E := (cell13204 ⟨36, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (20707016533759 / 25000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (219329560643 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_37 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (10349256208349 / 12500000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193299623039 / 100000000000000 : ℝ))
      (E := (cell13204 ⟨37, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (10349256208349 / 12500000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (2193299623039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_38 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (82760056818291 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (43866073473 / 2000000000000 : ℝ))
      (E := (cell13204 ⟨38, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (82760056818291 / 100000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (43866073473 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13204_39 : CellCertificate 13204 (10914079361847 / 125000000000000 : ℝ) (318148517078643 / 200000000000000000 : ℝ) (160516528035169 / 5000000000000000 : ℝ)
    (cell13204 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · norm_num [cell13204]
  · have h := gap_lower (n := 13204) (a := (16545217511889 / 20000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (1096653849579 / 50000000000000 : ℝ))
      (E := (cell13204 ⟨39, by decide⟩).energy) (xi := (160516528035169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13204 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13204]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13204])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13204) (a := (16545217511889 / 20000000000000 : ℝ)) (b := (77963642799 / 50000000000000 : ℝ)) (q := (1096653849579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13204])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13204]

theorem cert13205_20 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (83375553195681 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193121433589 / 100000000000000 : ℝ))
      (E := (cell13205 ⟨20, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (83375553195681 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193121433589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_21 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (10417644324777 / 12500000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193125448419 / 100000000000000 : ℝ))
      (E := (cell13205 ⟨21, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (10417644324777 / 12500000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193125448419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_22 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (83306780123311 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (21931294723 / 1000000000000 : ℝ))
      (E := (cell13205 ⟨22, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (83306780123311 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (21931294723 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_23 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (83272429738317 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193133450147 / 100000000000000 : ℝ))
      (E := (cell13205 ⟨23, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (83272429738317 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193133450147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_24 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (83238103410757 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (438627500361 / 20000000000000 : ℝ))
      (E := (cell13205 ⟨24, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (83238103410757 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (438627500361 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_25 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (20800950277079 / 25000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (1096570756651 / 50000000000000 : ℝ))
      (E := (cell13205 ⟨25, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (20800950277079 / 25000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (1096570756651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_26 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (83169522798847 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (1096572772821 / 50000000000000 : ℝ))
      (E := (cell13205 ⟨26, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (83169522798847 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (1096572772821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_27 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (83135268450367 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193149542713 / 100000000000000 : ℝ))
      (E := (cell13205 ⟨27, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (83135268450367 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193149542713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_28 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (83101038031057 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (137072097819 / 6250000000000 : ℝ))
      (E := (cell13205 ⟨28, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (83101038031057 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (137072097819 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_29 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (83066831509257 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193157556197 / 100000000000000 : ℝ))
      (E := (cell13205 ⟨29, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (83066831509257 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193157556197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_30 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (41516324426737 / 50000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (438632315233 / 20000000000000 : ℝ))
      (E := (cell13205 ⟨30, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (41516324426737 / 50000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (438632315233 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_31 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (82998490032369 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (274145703309 / 12500000000000 : ℝ))
      (E := (cell13205 ⟨31, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (82998490032369 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (274145703309 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_32 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (5185272188423 / 6250000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (1096584824869 / 50000000000000 : ℝ))
      (E := (cell13205 ⟨32, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (5185272188423 / 6250000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (1096584824869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_33 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (82930243769651 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (21931736469 / 1000000000000 : ℝ))
      (E := (cell13205 ⟨33, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (82930243769651 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (21931736469 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_34 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (82896156266159 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (1096588838661 / 50000000000000 : ℝ))
      (E := (cell13205 ⟨34, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (82896156266159 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (1096588838661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_35 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (82862092473587 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (1096590841441 / 50000000000000 : ℝ))
      (E := (cell13205 ⟨35, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (82862092473587 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (1096590841441 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_36 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (20707013090347 / 25000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (109659286127 / 5000000000000 : ℝ))
      (E := (cell13205 ⟨36, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (20707013090347 / 25000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (109659286127 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_37 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (41397017949583 / 50000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193189737683 / 100000000000000 : ℝ))
      (E := (cell13205 ⟨37, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (41397017949583 / 50000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (2193189737683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_38 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (82760043056681 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (17134326001 / 781250000000 : ℝ))
      (E := (cell13205 ⟨38, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (82760043056681 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (17134326001 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13205_39 : CellCertificate 13205 (174620084422719 / 2000000000000000 : ℝ) (1590622082128559 / 1000000000000000000 : ℝ) (6420163865013 / 200000000000000 : ℝ)
    (cell13205 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · norm_num [cell13205]
  · have h := gap_lower (n := 13205) (a := (82726073803847 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (27414971903 / 1250000000000 : ℝ))
      (E := (cell13205 ⟨39, by decide⟩).energy) (xi := (6420163865013 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13205 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13205]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13205])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13205) (a := (82726073803847 / 100000000000000 : ℝ)) (b := (77957671751 / 50000000000000 : ℝ)) (q := (27414971903 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13205])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13205]

theorem cert13206_20 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (41687769663549 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096505758487 / 50000000000000 : ℝ))
      (E := (cell13206 ⟨20, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (41687769663549 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096505758487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_21 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (10417642591967 / 12500000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2193015529573 / 100000000000000 : ℝ))
      (E := (cell13206 ⟨21, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (10417642591967 / 12500000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2193015529573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_22 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (5206672891683 / 6250000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (219301955127 / 10000000000000 : ℝ))
      (E := (cell13206 ⟨22, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (5206672891683 / 6250000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (219301955127 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_23 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (83272415888027 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (17544188683 / 800000000000 : ℝ))
      (E := (cell13206 ⟨23, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (83272415888027 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (17544188683 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_24 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (41619044783277 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096513788273 / 50000000000000 : ℝ))
      (E := (cell13206 ⟨24, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (41619044783277 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096513788273 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_25 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (41601893635097 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096515822221 / 50000000000000 : ℝ))
      (E := (cell13206 ⟨25, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (41601893635097 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096515822221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_26 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (41584754483401 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (109651780817 / 5000000000000 : ℝ))
      (E := (cell13206 ⟨26, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (41584754483401 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (109651780817 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_27 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (41567627312197 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (43860793399 / 2000000000000 : ℝ))
      (E := (cell13206 ⟨27, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (41567627312197 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (43860793399 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_28 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (1662020484223 / 2000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2193043690459 / 100000000000000 : ℝ))
      (E := (cell13206 ⟨28, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (1662020484223 / 2000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2193043690459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_29 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (20766704423853 / 25000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (548261919929 / 25000000000000 : ℝ))
      (E := (cell13206 ⟨29, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (20766704423853 / 25000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (548261919929 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_30 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (20758158761421 / 25000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (274131462237 / 12500000000000 : ℝ))
      (E := (cell13206 ⟨30, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (20758158761421 / 25000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (274131462237 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_31 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (8299847623063 / 10000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (109652787323 / 5000000000000 : ℝ))
      (E := (cell13206 ⟨31, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (8299847623063 / 10000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (109652787323 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_32 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (3318573648763 / 4000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2193059768029 / 100000000000000 : ℝ))
      (E := (cell13206 ⟨32, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (3318573648763 / 4000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (2193059768029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_33 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (82930229979999 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096531881771 / 50000000000000 : ℝ))
      (E := (cell13206 ⟨33, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (82930229979999 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096531881771 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_34 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (82896142482543 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (54826694809 / 2500000000000 : ℝ))
      (E := (cell13206 ⟨34, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (82896142482543 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (54826694809 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_35 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (41431039348001 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096535898181 / 50000000000000 : ℝ))
      (E := (cell13206 ⟨35, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (41431039348001 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096535898181 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_36 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (20707009647457 / 25000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (219307583451 / 10000000000000 : ℝ))
      (E := (cell13206 ⟨36, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (20707009647457 / 25000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (219307583451 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_37 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (82794022133627 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (548269962047 / 25000000000000 : ℝ))
      (E := (cell13206 ⟨37, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (82794022133627 / 100000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (548269962047 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_38 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (41380014648579 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096541918607 / 50000000000000 : ℝ))
      (E := (cell13206 ⟨38, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (41380014648579 / 50000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096541918607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13206_39 : CellCertificate 13206 (873074499035113 / 10000000000000000 : ℝ) (198812699639931 / 125000000000000000 : ℝ) (320983334304841 / 10000000000000000 : ℝ)
    (cell13206 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · norm_num [cell13206]
  · have h := gap_lower (n := 13206) (a := (16545212010067 / 20000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096543929977 / 50000000000000 : ℝ))
      (E := (cell13206 ⟨39, by decide⟩).energy) (xi := (320983334304841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13206 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13206]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13206])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13206) (a := (16545212010067 / 20000000000000 : ℝ)) (b := (77951701621 / 50000000000000 : ℝ)) (q := (1096543929977 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13206])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13206]

theorem cert13207_20 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (41687762730309 / 50000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (1096450827267 / 50000000000000 : ℝ))
      (E := (cell13207 ⟨20, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (41687762730309 / 50000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (1096450827267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_21 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (41670563437679 / 50000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192905664927 / 100000000000000 : ℝ))
      (E := (cell13207 ⟨21, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (41670563437679 / 50000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192905664927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_22 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (83306752412647 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192909684463 / 100000000000000 : ℝ))
      (E := (cell13207 ⟨22, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (83306752412647 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192909684463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_23 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (83272402039837 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (438582743291 / 20000000000000 : ℝ))
      (E := (cell13207 ⟨23, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (83272402039837 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (438582743291 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_24 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (83238075724449 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192917705559 / 100000000000000 : ℝ))
      (E := (cell13207 ⟨24, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (83238075724449 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192917705559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_25 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (83203773434171 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (1096460885717 / 50000000000000 : ℝ))
      (E := (cell13207 ⟨25, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (83203773434171 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (1096460885717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_26 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (16633899027371 / 20000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (1096462870679 / 50000000000000 : ℝ))
      (E := (cell13207 ⟨26, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (16633899027371 / 20000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (1096462870679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_27 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (83135240800517 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192929793041 / 100000000000000 : ℝ))
      (E := (cell13207 ⟨27, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (83135240800517 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192929793041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_28 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (41550505196669 / 50000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (219293381167 / 10000000000000 : ℝ))
      (E := (cell13207 ⟨28, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (41550505196669 / 50000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (219293381167 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_29 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (4153340194183 / 5000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (548234449773 / 25000000000000 : ℝ))
      (E := (cell13207 ⟨29, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (4153340194183 / 5000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (548234449773 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_30 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (20758155309997 / 25000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192941815483 / 100000000000000 : ℝ))
      (E := (cell13207 ⟨30, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (20758155309997 / 25000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192941815483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_31 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (10374807803873 / 12500000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (438589172461 / 20000000000000 : ℝ))
      (E := (cell13207 ⟨31, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (10374807803873 / 12500000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (438589172461 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_32 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (41482163712737 / 50000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (109647494109 / 5000000000000 : ℝ))
      (E := (cell13207 ⟨32, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (41482163712737 / 50000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (109647494109 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_33 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (41465108096219 / 50000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192953876043 / 100000000000000 : ℝ))
      (E := (cell13207 ⟨33, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (41465108096219 / 50000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192953876043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_34 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (82896128701017 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192957903259 / 100000000000000 : ℝ))
      (E := (cell13207 ⟨34, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (82896128701017 / 100000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192957903259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_35 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (41431032460253 / 50000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (274120238213 / 12500000000000 : ℝ))
      (E := (cell13207 ⟨35, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (41431032460253 / 50000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (274120238213 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_36 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (20707006205089 / 25000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192965942343 / 100000000000000 : ℝ))
      (E := (cell13207 ⟨36, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (20707006205089 / 25000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192965942343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_37 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (3311760334807 / 4000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192969954557 / 100000000000000 : ℝ))
      (E := (cell13207 ⟨37, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (3311760334807 / 4000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (2192969954557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_38 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (41380007769861 / 50000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (137060875057 / 6250000000000 : ℝ))
      (E := (cell13207 ⟨38, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (41380007769861 / 50000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (137060875057 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13207_39 : CellCertificate 13207 (27282768115983 / 312500000000000 : ℝ) (1590381130361731 / 1000000000000000000 : ℝ) (320958479231959 / 10000000000000000 : ℝ)
    (cell13207 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · norm_num [cell13207]
  · have h := gap_lower (n := 13207) (a := (20681511574727 / 25000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (438595604461 / 20000000000000 : ℝ))
      (E := (cell13207 ⟨39, by decide⟩).energy) (xi := (320958479231959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13207 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13207]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13207])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13207) (a := (20681511574727 / 25000000000000 : ℝ)) (b := (9743216551 / 6250000000000 : ℝ)) (q := (438595604461 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13207])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13207]

theorem cert13208_20 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (83375511596241 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192791787943 / 100000000000000 : ℝ))
      (E := (cell13208 ⟨20, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (83375511596241 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192791787943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_21 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (41670556508541 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192795854479 / 100000000000000 : ℝ))
      (E := (cell13208 ⟨21, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (41670556508541 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192795854479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_22 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (41653369280233 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (54819996797 / 2500000000000 : ℝ))
      (E := (cell13208 ⟨22, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (41653369280233 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (54819996797 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_23 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (41636194096873 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192803843387 / 100000000000000 : ℝ))
      (E := (cell13208 ⟨23, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (41636194096873 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192803843387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_24 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (20809515471111 / 25000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (548201972211 / 25000000000000 : ℝ))
      (E := (cell13208 ⟨24, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (20809515471111 / 25000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (548201972211 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_25 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (41601879800123 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192811894279 / 100000000000000 : ℝ))
      (E := (cell13208 ⟨25, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (41601879800123 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192811894279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_26 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (20792370327251 / 25000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (1096407960349 / 50000000000000 : ℝ))
      (E := (cell13208 ⟨26, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (20792370327251 / 25000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (1096407960349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_27 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (5195951686171 / 6250000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192819911987 / 100000000000000 : ℝ))
      (E := (cell13208 ⟨27, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (5195951686171 / 6250000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192819911987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_28 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (41550498288811 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (438564785747 / 20000000000000 : ℝ))
      (E := (cell13208 ⟨28, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (41550498288811 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (438564785747 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_29 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (83066790074003 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192827972861 / 100000000000000 : ℝ))
      (E := (cell13208 ⟨29, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (83066790074003 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192827972861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_30 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (16606521487277 / 20000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192831987489 / 100000000000000 : ℝ))
      (E := (cell13208 ⟨30, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (16606521487277 / 20000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192831987489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_31 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (8299844863343 / 10000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (1096418016297 / 50000000000000 : ℝ))
      (E := (cell13208 ⟨31, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (8299844863343 / 10000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (1096418016297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_32 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (20741078408491 / 25000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192840050797 / 100000000000000 : ℝ))
      (E := (cell13208 ⟨32, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (20741078408491 / 25000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192840050797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_33 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (82930202406967 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (548211010759 / 25000000000000 : ℝ))
      (E := (cell13208 ⟨33, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (82930202406967 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (548211010759 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_34 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (4144805746079 / 5000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192848068673 / 100000000000000 : ℝ))
      (E := (cell13208 ⟨34, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (4144805746079 / 5000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192848068673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_35 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (41431025573549 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (1096426034793 / 50000000000000 : ℝ))
      (E := (cell13208 ⟨35, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (41431025573549 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (1096426034793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_36 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (82828011052973 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (1096428052369 / 50000000000000 : ℝ))
      (E := (cell13208 ⟨36, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (82828011052973 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (1096428052369 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_37 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (8279399460881 / 10000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192860115513 / 100000000000000 : ℝ))
      (E := (cell13208 ⟨37, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (8279399460881 / 10000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192860115513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_38 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (82760001784371 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (548216040119 / 25000000000000 : ℝ))
      (E := (cell13208 ⟨38, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (82760001784371 / 100000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (548216040119 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13208_39 : CellCertificate 13208 (87302266414177 / 1000000000000000 : ℝ) (12423911576963 / 7812500000000000 : ℝ) (320933628031053 / 10000000000000000 : ℝ)
    (cell13208 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · norm_num [cell13208]
  · have h := gap_lower (n := 13208) (a := (41363016274783 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192868180521 / 100000000000000 : ℝ))
      (E := (cell13208 ⟨39, by decide⟩).energy) (xi := (320933628031053 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13208 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13208]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13208])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13208) (a := (41363016274783 / 50000000000000 : ℝ)) (b := (4871235257 / 3125000000000 : ℝ)) (q := (2192868180521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13208])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13208]

theorem cert13209_20 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (41687748866983 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (274085246941 / 12500000000000 : ℝ))
      (E := (cell13209 ⟨20, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (41687748866983 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (274085246941 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_21 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (41670549580453 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (1096342990767 / 50000000000000 : ℝ))
      (E := (cell13209 ⟨21, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (41670549580453 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (1096342990767 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_22 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (16661344942077 / 20000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (274086249597 / 12500000000000 : ℝ))
      (E := (cell13209 ⟨22, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (16661344942077 / 20000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (274086249597 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_23 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (16654474869951 / 20000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192694024567 / 100000000000000 : ℝ))
      (E := (cell13209 ⟨23, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (16654474869951 / 20000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192694024567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_24 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (83238048046537 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192698067983 / 100000000000000 : ℝ))
      (E := (cell13209 ⟨24, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (83238048046537 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192698067983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_25 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (41601872884209 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192702071423 / 100000000000000 : ℝ))
      (E := (cell13209 ⟨25, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (41601872884209 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192702071423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_26 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (332677869933 / 400000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192706095893 / 100000000000000 : ℝ))
      (E := (cell13209 ⟨26, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (332677869933 / 400000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192706095893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_27 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (1662704263181 / 2000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (13704438033 / 625000000000 : ℝ))
      (E := (cell13209 ⟨27, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (1662704263181 / 2000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (13704438033 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_28 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (83100982763999 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192714100173 / 100000000000000 : ℝ))
      (E := (cell13209 ⟨28, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (83100982763999 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192714100173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_29 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (83066776266439 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192718142489 / 100000000000000 : ℝ))
      (E := (cell13209 ⟨29, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (83066776266439 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192718142489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_30 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (41516296817437 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (438544431071 / 20000000000000 : ℝ))
      (E := (cell13209 ⟨30, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (41516296817437 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (438544431071 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_31 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (5187402177373 / 6250000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (1096363099371 / 50000000000000 : ℝ))
      (E := (cell13209 ⟨31, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (5187402177373 / 6250000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (1096363099371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_32 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (16592859968909 / 20000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (87709208611 / 4000000000000 : ℝ))
      (E := (cell13209 ⟨32, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (16592859968909 / 20000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (87709208611 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_33 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (41465094311793 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (219273420589 / 10000000000000 : ℝ))
      (E := (cell13209 ⟨33, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (41465094311793 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (219273420589 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_34 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (10362012643029 / 12500000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192738229949 / 100000000000000 : ℝ))
      (E := (cell13209 ⟨34, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (10362012643029 / 12500000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192738229949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_35 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (41431018687889 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192742229331 / 100000000000000 : ℝ))
      (E := (cell13209 ⟨35, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (41431018687889 / 50000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192742229331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_36 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (20706999321919 / 25000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (1096373131499 / 50000000000000 : ℝ))
      (E := (cell13209 ⟨36, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (20706999321919 / 25000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (1096373131499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_37 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (82793980849531 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (438550054467 / 20000000000000 : ℝ))
      (E := (cell13209 ⟨37, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (82793980849531 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (438550054467 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_38 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (16551997606221 / 20000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (438550863181 / 20000000000000 : ℝ))
      (E := (cell13209 ⟨38, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (16551997606221 / 20000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (438550863181 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13209_39 : CellCertificate 13209 (436498376162599 / 5000000000000000 : ℝ) (1590140251583901 / 1000000000000000000 : ℝ) (80227195175293 / 2500000000000000 : ℝ)
    (cell13209 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · norm_num [cell13209]
  · have h := gap_lower (n := 13209) (a := (82726018802309 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192758334603 / 100000000000000 : ℝ))
      (E := (cell13209 ⟨39, by decide⟩).energy) (xi := (80227195175293 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13209 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13209]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13209])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13209) (a := (82726018802309 / 100000000000000 : ℝ)) (b := (31173518693 / 20000000000000 : ℝ)) (q := (2192758334603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13209])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13209]

theorem cert13210_20 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (162842741941 / 195312500000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192572158963 / 100000000000000 : ℝ))
      (E := (cell13210 ⟨20, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (162842741941 / 195312500000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192572158963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_21 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (83341085306831 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192576162789 / 100000000000000 : ℝ))
      (E := (cell13210 ⟨21, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (83341085306831 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192576162789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_22 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (20826677715601 / 25000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192580175897 / 100000000000000 : ℝ))
      (E := (cell13210 ⟨22, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (20826677715601 / 25000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192580175897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_23 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (41636180253931 / 50000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192584201601 / 100000000000000 : ℝ))
      (E := (cell13210 ⟨23, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (41636180253931 / 50000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192584201601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_24 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (83238034210727 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192588242977 / 100000000000000 : ℝ))
      (E := (cell13210 ⟨24, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (83238034210727 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192588242977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_25 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (41601865969343 / 50000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096296122211 / 50000000000000 : ℝ))
      (E := (cell13210 ⟨25, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (41601865969343 / 50000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096296122211 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_26 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (83169453659591 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (34259316671 / 1562500000000 : ℝ))
      (E := (cell13210 ⟨26, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (83169453659591 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (34259316671 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_27 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (4156759967073 / 5000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192600312919 / 100000000000000 : ℝ))
      (E := (cell13210 ⟨27, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (4156759967073 / 5000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192600312919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_28 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (83100968952471 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192604325981 / 100000000000000 : ℝ))
      (E := (cell13210 ⟨28, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (83100968952471 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192604325981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_29 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (83066762460969 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096304153987 / 50000000000000 : ℝ))
      (E := (cell13210 ⟨29, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (83066762460969 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096304153987 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_30 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (1297384059929 / 1562500000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096306159539 / 50000000000000 : ℝ))
      (E := (cell13210 ⟨30, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (1297384059929 / 1562500000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096306159539 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_31 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (82998421044597 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (8770465443 / 400000000000 : ℝ))
      (E := (cell13210 ⟨31, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (82998421044597 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (8770465443 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_32 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (324079242411 / 390625000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096310187807 / 50000000000000 : ℝ))
      (E := (cell13210 ⟨32, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (324079242411 / 390625000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096310187807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_33 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (16586034968459 / 20000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (548156105809 / 25000000000000 : ℝ))
      (E := (cell13210 ⟨33, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (16586034968459 / 20000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (548156105809 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_34 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (82896087368973 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096314222871 / 50000000000000 : ℝ))
      (E := (cell13210 ⟨34, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (82896087368973 / 100000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096314222871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_35 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (41431011803273 / 50000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192632443617 / 100000000000000 : ℝ))
      (E := (cell13210 ⟨35, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (41431011803273 / 50000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (2192632443617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_36 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (41413991762233 / 50000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (137039779739 / 6250000000000 : ℝ))
      (E := (cell13210 ⟨36, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (41413991762233 / 50000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (137039779739 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_37 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (41396983546169 / 50000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096320241873 / 50000000000000 : ℝ))
      (E := (cell13210 ⟨37, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (41396983546169 / 50000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (1096320241873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_38 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (20689993569981 / 25000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (548161131487 / 25000000000000 : ℝ))
      (E := (cell13210 ⟨38, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (20689993569981 / 25000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (548161131487 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13210_39 : CellCertificate 13210 (436485422130443 / 5000000000000000 : ℝ) (1590019839555497 / 1000000000000000000 : ℝ) (160441968620683 / 5000000000000000 : ℝ)
    (cell13210 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · norm_num [cell13210]
  · have h := gap_lower (n := 13210) (a := (16545201011427 / 20000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (87705941733 / 4000000000000 : ℝ))
      (E := (cell13210 ⟨39, by decide⟩).energy) (xi := (160441968620683 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13210 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13210]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13210])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13210) (a := (16545201011427 / 20000000000000 : ℝ)) (b := (7792783027 / 5000000000000 : ℝ)) (q := (87705941733 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13210])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13210]

theorem cert13211_20 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (41687735007859 / 50000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192462396579 / 100000000000000 : ℝ))
      (E := (cell13211 ⟨20, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (41687735007859 / 50000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192462396579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_21 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (10417633931857 / 12500000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192466398247 / 100000000000000 : ℝ))
      (E := (cell13211 ⟨21, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (10417633931857 / 12500000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192466398247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_22 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (83306697016521 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (1096235204623 / 50000000000000 : ℝ))
      (E := (cell13211 ⟨22, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (83306697016521 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (1096235204623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_23 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (83272346668067 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192474432887 / 100000000000000 : ℝ))
      (E := (cell13211 ⟨23, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (83272346668067 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192474432887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_24 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (16647604075403 / 20000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (1096239236123 / 50000000000000 : ℝ))
      (E := (cell13211 ⟨24, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (16647604075403 / 20000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (1096239236123 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_25 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (83203718111051 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192482471721 / 100000000000000 : ℝ))
      (E := (cell13211 ⟨25, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (83203718111051 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192482471721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_26 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (20792359959507 / 25000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (13703040577 / 625000000000 : ℝ))
      (E := (cell13211 ⟨26, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (20792359959507 / 25000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (13703040577 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_27 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (83135185525963 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (274061309741 / 12500000000000 : ℝ))
      (E := (cell13211 ⟨27, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (83135185525963 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (274061309741 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_28 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (83100955143037 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (1096247244567 / 50000000000000 : ℝ))
      (E := (cell13211 ⟨28, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (83100955143037 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (1096247244567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_29 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (83066748657591 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (1096249263929 / 50000000000000 : ℝ))
      (E := (cell13211 ⟨29, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (83066748657591 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (1096249263929 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_30 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (8303256603813 / 10000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192502537223 / 100000000000000 : ℝ))
      (E := (cell13211 ⟨30, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (8303256603813 / 10000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192502537223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_31 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (82998407253317 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (548126644301 / 25000000000000 : ℝ))
      (E := (cell13211 ⟨31, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (82998407253317 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (548126644301 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_32 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (82964272271977 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192510590423 / 100000000000000 : ℝ))
      (E := (cell13211 ⟨32, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (82964272271977 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192510590423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_33 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (20732540265773 / 25000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192514636447 / 100000000000000 : ℝ))
      (E := (cell13211 ⟨33, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (20732540265773 / 25000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192514636447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_34 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (82896073595801 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192518657401 / 100000000000000 : ℝ))
      (E := (cell13211 ⟨34, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (82896073595801 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192518657401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_35 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (82862009839401 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192522653769 / 100000000000000 : ℝ))
      (E := (cell13211 ⟨35, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (82862009839401 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192522653769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_36 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (41413984881671 / 50000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (548131671129 / 25000000000000 : ℝ))
      (E := (cell13211 ⟨36, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (41413984881671 / 50000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (548131671129 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_37 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (82793953337231 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (137033168189 / 6250000000000 : ℝ))
      (E := (cell13211 ⟨37, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (82793953337231 / 100000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (137033168189 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_38 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (20689990132707 / 25000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192534731859 / 100000000000000 : ℝ))
      (E := (cell13211 ⟨38, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (20689990132707 / 25000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (2192534731859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13211_39 : CellCertificate 13211 (436472469973989 / 5000000000000000 : ℝ) (397474861440477 / 250000000000000000 : ℝ) (160429548825343 / 5000000000000000 : ℝ)
    (cell13211 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · norm_num [cell13211]
  · have h := gap_lower (n := 13211) (a := (16545198262809 / 20000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (1096269373957 / 50000000000000 : ℝ))
      (E := (cell13211 ⟨39, by decide⟩).energy) (xi := (160429548825343 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13211 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13211]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13211])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13211) (a := (16545198262809 / 20000000000000 : ℝ)) (b := (155843729447 / 100000000000000 : ℝ)) (q := (1096269373957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13211])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13211]

theorem cert13212_20 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (41687728079873 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192352630047 / 100000000000000 : ℝ))
      (E := (cell13212 ⟨20, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (41687728079873 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192352630047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_21 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (4167052880249 / 5000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192356629561 / 100000000000000 : ℝ))
      (E := (cell13212 ⟨21, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (4167052880249 / 5000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192356629561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_22 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (41653341586369 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (43847212769 / 2000000000000 : ℝ))
      (E := (cell13212 ⟨22, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (41653341586369 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (43847212769 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_23 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (8327233283037 / 10000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192364660029 / 100000000000000 : ℝ))
      (E := (cell13212 ⟨23, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (8327233283037 / 10000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192364660029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_24 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (83238006545399 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (548092174343 / 25000000000000 : ℝ))
      (E := (cell13212 ⟨24, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (83238006545399 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (548092174343 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_25 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (10400463035689 / 12500000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (1096186347439 / 50000000000000 : ℝ))
      (E := (cell13212 ⟨25, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (10400463035689 / 12500000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (1096186347439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_26 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (64976114077 / 78125000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192376713553 / 100000000000000 : ℝ))
      (E := (cell13212 ⟨26, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (64976114077 / 78125000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192376713553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_27 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (83135171712561 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (438476139457 / 20000000000000 : ℝ))
      (E := (cell13212 ⟨27, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (83135171712561 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (438476139457 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_28 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (16620188267139 / 20000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192384765177 / 100000000000000 : ℝ))
      (E := (cell13212 ⟨28, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (16620188267139 / 20000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192384765177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_29 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (16613346971261 / 20000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (1096194371801 / 50000000000000 : ℝ))
      (E := (cell13212 ⟨29, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (16613346971261 / 20000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (1096194371801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_30 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (41516276121447 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (34256137653 / 1562500000000 : ℝ))
      (E := (cell13212 ⟨30, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (41516276121447 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (34256137653 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_31 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (82998393464127 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192396789521 / 100000000000000 : ℝ))
      (E := (cell13212 ⟨31, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (82998393464127 / 100000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192396789521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_32 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (20741064622207 / 25000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (438480160219 / 20000000000000 : ℝ))
      (E := (cell13212 ⟨32, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (20741064622207 / 25000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (438480160219 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_33 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (41465073642989 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192404845521 / 100000000000000 : ℝ))
      (E := (cell13212 ⟨33, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (41465073642989 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192404845521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_34 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (41448029912359 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192408864923 / 100000000000000 : ℝ))
      (E := (cell13212 ⟨34, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (41448029912359 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192408864923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_35 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (41430998037171 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192412859787 / 100000000000000 : ℝ))
      (E := (cell13212 ⟨35, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (41430998037171 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192412859787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_36 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (5176747250269 / 6250000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (1096208444537 / 50000000000000 : ℝ))
      (E := (cell13212 ⟨36, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (5176747250269 / 6250000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (1096208444537 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_37 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (5174621224013 / 6250000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (219242089417 / 10000000000000 : ℝ))
      (E := (cell13212 ⟨37, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (5174621224013 / 6250000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (219242089417 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_38 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (16551989356763 / 20000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (1096212466819 / 50000000000000 : ℝ))
      (E := (cell13212 ⟨38, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (16551989356763 / 20000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (1096212466819 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13212_39 : CellCertificate 13212 (43645951969281 / 500000000000000 : ℝ) (794889535099497 / 500000000000000000 : ℝ) (160417130964091 / 5000000000000000 : ℝ)
    (cell13212 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · norm_num [cell13212]
  · have h := gap_lower (n := 13212) (a := (41362988786519 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192428948373 / 100000000000000 : ℝ))
      (E := (cell13212 ⟨39, by decide⟩).energy) (xi := (160417130964091 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13212 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13212]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13212])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13212) (a := (41362988786519 / 50000000000000 : ℝ)) (b := (77915900093 / 50000000000000 : ℝ)) (q := (2192428948373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13212])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13212]

theorem cert13213_20 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (83375442305873 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192242859369 / 100000000000000 : ℝ))
      (E := (cell13213 ⟨20, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (83375442305873 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192242859369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_21 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (20835260939301 / 25000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (274030857091 / 12500000000000 : ℝ))
      (E := (cell13213 ⟨21, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (20835260939301 / 25000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (274030857091 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_22 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (20826667332763 / 25000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (219225086351 / 10000000000000 : ℝ))
      (E := (cell13213 ⟨22, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (20826667332763 / 25000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (219225086351 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_23 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (8327231899477 / 10000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192254883027 / 100000000000000 : ℝ))
      (E := (cell13213 ⟨23, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (8327231899477 / 10000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192254883027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_24 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (2080949817897 / 2500000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (438451783671 / 20000000000000 : ℝ))
      (E := (cell13213 ⟨24, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (2080949817897 / 2500000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (438451783671 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_25 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (20800922615517 / 25000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (548065728473 / 25000000000000 : ℝ))
      (E := (cell13213 ⟨25, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (20800922615517 / 25000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (548065728473 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_26 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (41584706100593 / 50000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (1096133465323 / 50000000000000 : ℝ))
      (E := (cell13213 ⟨26, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (41584706100593 / 50000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (1096133465323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_27 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (20783789475313 / 25000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192270970993 / 100000000000000 : ℝ))
      (E := (cell13213 ⟨27, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (20783789475313 / 25000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192270970993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_28 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (41550463765223 / 50000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (438454995713 / 20000000000000 : ℝ))
      (E := (cell13213 ⟨28, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (41550463765223 / 50000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (438454995713 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_29 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (83066721057111 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (1096139506873 / 50000000000000 : ℝ))
      (E := (cell13213 ⟨29, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (83066721057111 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (1096139506873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_30 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (332130153799 / 400000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192283019661 / 100000000000000 : ℝ))
      (E := (cell13213 ⟨30, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (332130153799 / 400000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192283019661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_31 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (82998379677027 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (438457411257 / 20000000000000 : ℝ))
      (E := (cell13213 ⟨31, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (82998379677027 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (438457411257 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_32 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (82964244707767 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (3425454791 / 156250000000 : ℝ))
      (E := (cell13213 ⟨32, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (82964244707767 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (3425454791 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_33 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (10366266688869 / 12500000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (548073777273 / 25000000000000 : ℝ))
      (E := (cell13213 ⟨33, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (10366266688869 / 12500000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (548073777273 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_34 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (82896046055721 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192299126967 / 100000000000000 : ℝ))
      (E := (cell13213 ⟨34, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (82896046055721 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192299126967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_35 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (8286198231137 / 10000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192303120349 / 100000000000000 : ℝ))
      (E := (cell13213 ⟨35, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (8286198231137 / 10000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192303120349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_36 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (82827942247351 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (1096153574101 / 50000000000000 : ℝ))
      (E := (cell13213 ⟨36, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (82827942247351 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (1096153574101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_37 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (82793925833269 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192311151909 / 100000000000000 : ℝ))
      (E := (cell13213 ⟨37, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (82793925833269 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (2192311151909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_38 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (41379966519443 / 50000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (438463038007 / 20000000000000 : ℝ))
      (E := (cell13213 ⟨38, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (41379966519443 / 50000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (438463038007 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13213_39 : CellCertificate 13213 (872893142572957 / 10000000000000000 : ℝ) (794829356431307 / 500000000000000000 : ℝ) (64161886014581 / 2000000000000000 : ℝ)
    (cell13213 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · norm_num [cell13213]
  · have h := gap_lower (n := 13213) (a := (82725963834113 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (87692768139 / 4000000000000 : ℝ))
      (E := (cell13213 ⟨39, by decide⟩).energy) (xi := (64161886014581 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13213 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13213]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13213])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13213) (a := (82725963834113 / 100000000000000 : ℝ)) (b := (155819872757 / 100000000000000 : ℝ)) (q := (87692768139 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13213])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13213]

theorem cert13214_20 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (833754284541 / 1000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (438426616909 / 20000000000000 : ℝ))
      (E := (cell13214 ⟨20, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (833754284541 / 1000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (438426616909 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_21 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (41670514955763 / 50000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192137138101 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨21, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (41670514955763 / 50000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192137138101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_22 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (10413331936433 / 12500000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192141142799 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨22, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (10413331936433 / 12500000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192141142799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_23 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (83272305161267 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192145160279 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨23, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (83272305161267 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192145160279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_24 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (10404747361057 / 12500000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192149193617 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨24, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (10404747361057 / 12500000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192149193617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_25 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (41601838320359 / 50000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (219215318721 / 10000000000000 : ℝ))
      (E := (cell13214 ⟨25, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (41601838320359 / 50000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (219215318721 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_26 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (41584699192953 / 50000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (1096078601033 / 50000000000000 : ℝ))
      (E := (cell13214 ⟨26, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (41584699192953 / 50000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (1096078601033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_27 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (20783786023009 / 25000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (1096080620281 / 50000000000000 : ℝ))
      (E := (cell13214 ⟨27, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (20783786023009 / 25000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (1096080620281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_28 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (83100913727289 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192165246329 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨28, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (83100913727289 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192165246329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_29 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (10383338407501 / 12500000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192169279751 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨29, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (10383338407501 / 12500000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192169279751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_30 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (16606504931739 / 20000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (438434656791 / 20000000000000 : ℝ))
      (E := (cell13214 ⟨30, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (16606504931739 / 20000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (438434656791 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_31 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (82998365892017 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2140798163 / 97656250000 : ℝ))
      (E := (cell13214 ⟨31, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (82998365892017 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2140798163 / 97656250000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_32 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (16592846185759 / 20000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192181327249 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨32, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (16592846185759 / 20000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192181327249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_33 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (41465059869007 / 50000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (137011585533 / 6250000000000 : ℝ))
      (E := (cell13214 ⟨33, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (41465059869007 / 50000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (137011585533 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_34 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (82896032288811 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (548047346219 / 25000000000000 : ℝ))
      (E := (cell13214 ⟨34, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (82896032288811 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (548047346219 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_35 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (82861968550483 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192193376779 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨35, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (82861968550483 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192193376779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_36 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (82827928492483 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192197403197 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨36, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (82827928492483 / 100000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192197403197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_37 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (16558782416883 / 20000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192201405517 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨37, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (16558782416883 / 20000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192201405517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_38 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (2068997982401 / 2500000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (1096102721151 / 50000000000000 : ℝ))
      (E := (cell13214 ⟨38, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (2068997982401 / 2500000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (1096102721151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13214_39 : CellCertificate 13214 (436433624754567 / 5000000000000000 : ℝ) (397384593437157 / 250000000000000000 : ℝ) (320784602083907 / 10000000000000000 : ℝ)
    (cell13214 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · norm_num [cell13214]
  · have h := gap_lower (n := 13214) (a := (8272595009727 / 10000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192209454447 / 100000000000000 : ℝ))
      (E := (cell13214 ⟨39, by decide⟩).energy) (xi := (320784602083907 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13214 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13214]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13214])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13214) (a := (8272595009727 / 10000000000000 : ℝ)) (b := (3895198679 / 2500000000000 : ℝ)) (q := (2192209454447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13214])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13214]

theorem cert13215_20 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (3335016584177 / 4000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (1096011711117 / 50000000000000 : ℝ))
      (E := (cell13215 ⟨20, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (3335016584177 / 4000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (1096011711117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_21 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (41670508033973 / 50000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192027415331 / 100000000000000 : ℝ))
      (E := (cell13215 ⟨21, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (41670508033973 / 50000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192027415331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_22 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (83306641653973 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192031417947 / 100000000000000 : ℝ))
      (E := (cell13215 ⟨22, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (83306641653973 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192031417947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_23 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (4163614566493 / 5000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192035433391 / 100000000000000 : ℝ))
      (E := (cell13215 ⟨23, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (4163614566493 / 5000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192035433391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_24 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (10404745632891 / 12500000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (1096019732369 / 50000000000000 : ℝ))
      (E := (cell13215 ⟨24, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (10404745632891 / 12500000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (1096019732369 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_25 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (10400457852683 / 12500000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (137002719677 / 6250000000000 : ℝ))
      (E := (cell13215 ⟨25, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (10400457852683 / 12500000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (137002719677 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_26 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (1039617307159 / 1250000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (438409505563 / 20000000000000 : ℝ))
      (E := (cell13215 ⟨26, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (1039617307159 / 1250000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (438409505563 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_27 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (83135130284913 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192051505993 / 100000000000000 : ℝ))
      (E := (cell13215 ⟨27, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (83135130284913 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192051505993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_28 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (5193806245389 / 6250000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192055568471 / 100000000000000 : ℝ))
      (E := (cell13215 ⟨28, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (5193806245389 / 6250000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192055568471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_29 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (16613338692999 / 20000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (1096029770811 / 50000000000000 : ℝ))
      (E := (cell13215 ⟨29, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (16613338692999 / 20000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (1096029770811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_30 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (83032510869731 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (87682544107 / 4000000000000 : ℝ))
      (E := (cell13215 ⟨30, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (83032510869731 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (87682544107 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_31 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (16599670421819 / 20000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192067577407 / 100000000000000 : ℝ))
      (E := (cell13215 ⟨31, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (16599670421819 / 20000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192067577407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_32 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (82964217151911 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192071642733 / 100000000000000 : ℝ))
      (E := (cell13215 ⟨32, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (82964217151911 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (2192071642733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_33 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (41465052983581 / 50000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (274009452979 / 12500000000000 : ℝ))
      (E := (cell13215 ⟨33, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (41465052983581 / 50000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (274009452979 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_34 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (82896018523987 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (438415927731 / 20000000000000 : ℝ))
      (E := (cell13215 ⟨34, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (82896018523987 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (438415927731 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_35 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (41430977395841 / 50000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (548020921939 / 25000000000000 : ℝ))
      (E := (cell13215 ⟨35, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (41430977395841 / 50000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (548020921939 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_36 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (82827914739699 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (1096043856383 / 50000000000000 : ℝ))
      (E := (cell13215 ⟨36, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (82827914739699 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (1096043856383 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_37 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (82793898337643 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (1096045856861 / 50000000000000 : ℝ))
      (E := (cell13215 ⟨37, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (82793898337643 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (1096045856861 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_38 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (20689976388819 / 25000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (219209574919 / 10000000000000 : ℝ))
      (E := (cell13215 ⟨38, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (20689976388819 / 25000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (219209574919 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13215_39 : CellCertificate 13215 (872841360193299 / 10000000000000000 : ℝ) (794709026426449 / 500000000000000000 : ℝ) (160379888980119 / 5000000000000000 : ℝ)
    (cell13215 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · norm_num [cell13215]
  · have h := gap_lower (n := 13215) (a := (82725936362509 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (34251558751 / 1562500000000 : ℝ))
      (E := (cell13215 ⟨39, by decide⟩).energy) (xi := (160379888980119 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13215 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13215]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13215])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13215) (a := (82725936362509 / 100000000000000 : ℝ)) (b := (155796023393 / 100000000000000 : ℝ)) (q := (34251558751 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13215])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13215]

theorem cert13216_20 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (83375400756849 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (43838273949 / 2000000000000 : ℝ))
      (E := (cell13216 ⟨20, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (83375400756849 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (43838273949 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_21 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (83341002226463 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191917746771 / 100000000000000 : ℝ))
      (E := (cell13216 ⟨21, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (83341002226463 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191917746771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_22 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (83306627818579 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191921747327 / 100000000000000 : ℝ))
      (E := (cell13216 ⟨22, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (83306627818579 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191921747327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_23 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (83272277500549 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (1095962880379 / 50000000000000 : ℝ))
      (E := (cell13216 ⟨23, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (83272277500549 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (1095962880379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_24 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (41618975619947 / 50000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191929790141 / 100000000000000 : ℝ))
      (E := (cell13216 ⟨24, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (41618975619947 / 50000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191929790141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_25 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (83203649004303 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191933779871 / 100000000000000 : ℝ))
      (E := (cell13216 ⟨25, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (83203649004303 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191933779871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_26 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (41584685380813 / 50000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (1095968895479 / 50000000000000 : ℝ))
      (E := (cell13216 ⟨26, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (41584685380813 / 50000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (1095968895479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_27 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (41567558239941 / 50000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191941825777 / 100000000000000 : ℝ))
      (E := (cell13216 ⟨27, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (41567558239941 / 50000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191941825777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_28 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (332403544509 / 400000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191945827961 / 100000000000000 : ℝ))
      (E := (cell13216 ⟨28, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (332403544509 / 400000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191945827961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_29 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (83066679672073 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (1095974928947 / 50000000000000 : ℝ))
      (E := (cell13216 ⟨29, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (83066679672073 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (1095974928947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_30 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (10379062135357 / 12500000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191953858699 / 100000000000000 : ℝ))
      (E := (cell13216 ⟨30, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (10379062135357 / 12500000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191953858699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_31 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (82998338328261 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (136997368147 / 6250000000000 : ℝ))
      (E := (cell13216 ⟨31, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (82998338328261 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (136997368147 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_32 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (16592840675423 / 20000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (87678475819 / 4000000000000 : ℝ))
      (E := (cell13216 ⟨32, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (16592840675423 / 20000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (87678475819 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_33 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (82930092198397 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (438393186727 / 20000000000000 : ℝ))
      (E := (cell13216 ⟨33, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (82930092198397 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (438393186727 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_34 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (82896004761249 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191969946957 / 100000000000000 : ℝ))
      (E := (cell13216 ⟨34, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (82896004761249 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191969946957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_35 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (16572388206993 / 20000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (547993498651 / 25000000000000 : ℝ))
      (E := (cell13216 ⟨35, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (16572388206993 / 20000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (547993498651 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_36 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (82827900988999 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (547994504551 / 25000000000000 : ℝ))
      (E := (cell13216 ⟨36, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (82827900988999 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (547994504551 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_37 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (16558776918591 / 20000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (1095991008899 / 50000000000000 : ℝ))
      (E := (cell13216 ⟨37, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (16558776918591 / 20000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (1095991008899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_38 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (41379945908297 / 50000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (43839721039 / 2000000000000 : ℝ))
      (E := (cell13216 ⟨38, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (41379945908297 / 50000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (43839721039 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13216_39 : CellCertificate 13216 (218203868656149 / 2500000000000000 : ℝ) (198662218771411 / 125000000000000000 : ℝ) (40091869712619 / 1250000000000000 : ℝ)
    (cell13216 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · norm_num [cell13216]
  · have h := gap_lower (n := 13216) (a := (82725922629829 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191990061553 / 100000000000000 : ℝ))
      (E := (cell13216 ⟨39, by decide⟩).energy) (xi := (40091869712619 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13216 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13216]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13216])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13216) (a := (82725922629829 / 100000000000000 : ℝ)) (b := (155784101457 / 100000000000000 : ℝ)) (q := (2191990061553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13216])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13216]

theorem cert13217_20 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (20843846727843 / 25000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191804026851 / 100000000000000 : ℝ))
      (E := (cell13217 ⟨20, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (20843846727843 / 25000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191804026851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_21 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (41670494193539 / 50000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191808015717 / 100000000000000 : ℝ))
      (E := (cell13217 ⟨21, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (41670494193539 / 50000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191808015717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_22 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (83306613985281 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (1095906036283 / 50000000000000 : ℝ))
      (E := (cell13217 ⟨22, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (83306613985281 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (1095906036283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_23 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (83272263673333 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191816083987 / 100000000000000 : ℝ))
      (E := (cell13217 ⟨23, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (83272263673333 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191816083987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_24 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (16647587483751 / 20000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (438364022281 / 20000000000000 : ℝ))
      (E := (cell13217 ⟨24, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (16647587483751 / 20000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (438364022281 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_25 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (16640727037847 / 20000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (1095912049609 / 50000000000000 : ℝ))
      (E := (cell13217 ⟨25, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (16640727037847 / 20000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (1095912049609 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_26 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (665354855621 / 800000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (136989256777 / 6250000000000 : ℝ))
      (E := (cell13217 ⟨26, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (665354855621 / 800000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (136989256777 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_27 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (41567551338471 / 50000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191832141427 / 100000000000000 : ℝ))
      (E := (cell13217 ⟨27, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (41567551338471 / 50000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191832141427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_28 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (41550436165183 / 50000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (273979517729 / 12500000000000 : ℝ))
      (E := (cell13217 ⟨28, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (41550436165183 / 50000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (273979517729 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_29 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (83066665881241 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191840170031 / 100000000000000 : ℝ))
      (E := (cell13217 ⟨29, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (83066665881241 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191840170031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_30 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (83032483298069 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191844227713 / 100000000000000 : ℝ))
      (E := (cell13217 ⟨30, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (83032483298069 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191844227713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_31 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (20749581137379 / 25000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (547962049791 / 25000000000000 : ℝ))
      (E := (cell13217 ⟨31, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (20749581137379 / 25000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (547962049791 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_32 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (16592837920881 / 20000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191852261303 / 100000000000000 : ℝ))
      (E := (cell13217 ⟨32, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (16592837920881 / 20000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191852261303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_33 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (41465039215859 / 50000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (547964059827 / 25000000000000 : ℝ))
      (E := (cell13217 ⟨33, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (41465039215859 / 50000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (547964059827 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_34 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (20723997750149 / 25000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (273982538723 / 12500000000000 : ℝ))
      (E := (cell13217 ⟨34, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (20723997750149 / 25000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (273982538723 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_35 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (82861927280333 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191864297321 / 100000000000000 : ℝ))
      (E := (cell13217 ⟨35, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (82861927280333 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (2191864297321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_36 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (41413943620191 / 50000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (1095934159757 / 50000000000000 : ℝ))
      (E := (cell13217 ⟨36, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (41413943620191 / 50000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (1095934159757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_37 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (82793870850349 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (1095936158873 / 50000000000000 : ℝ))
      (E := (cell13217 ⟨37, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (82793870850349 / 100000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (1095936158873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_38 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (41379939039997 / 50000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (1095938175291 / 50000000000000 : ℝ))
      (E := (cell13217 ⟨38, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (41379939039997 / 50000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (1095938175291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13217_39 : CellCertificate 13217 (872789592802173 / 10000000000000000 : ℝ) (1589177465699661 / 1000000000000000000 : ℝ) (3207101413051 / 100000000000000 : ℝ)
    (cell13217 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · norm_num [cell13217]
  · have h := gap_lower (n := 13217) (a := (8272590889923 / 10000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (547970089729 / 25000000000000 : ℝ))
      (E := (cell13217 ⟨39, by decide⟩).energy) (xi := (3207101413051 / 100000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13217 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13217]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13217])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13217) (a := (8272590889923 / 10000000000000 : ℝ)) (b := (155772181351 / 100000000000000 : ℝ)) (q := (547970089729 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13217])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13217]

theorem cert13218_20 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (83375373067991 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191694352113 / 100000000000000 : ℝ))
      (E := (cell13218 ⟨20, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (83375373067991 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191694352113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_21 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (83340974549789 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (87667935889 / 4000000000000 : ℝ))
      (E := (cell13218 ⟨21, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (83340974549789 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (87667935889 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_22 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (41653300077039 / 50000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191702393667 / 100000000000000 : ℝ))
      (E := (cell13218 ⟨22, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (41653300077039 / 50000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191702393667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_23 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (20818062462053 / 25000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (547926600769 / 25000000000000 : ℝ))
      (E := (cell13218 ⟨23, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (20818062462053 / 25000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (547926600769 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_24 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (8323792359971 / 10000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (219171042853 / 10000000000000 : ℝ))
      (E := (cell13218 ⟨24, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (8323792359971 / 10000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (219171042853 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_25 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (83203621376261 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (219171447287 / 10000000000000 : ℝ))
      (E := (cell13218 ⟨25, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (83203621376261 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (219171447287 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_26 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (20792335786429 / 25000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (1095859240119 / 50000000000000 : ℝ))
      (E := (cell13218 ⟨26, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (20792335786429 / 25000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (1095859240119 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_27 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (83135088876093 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (273965313929 / 12500000000000 : ℝ))
      (E := (cell13218 ⟨27, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (83135088876093 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (273965313929 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_28 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (83100858535573 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (1095863255041 / 50000000000000 : ℝ))
      (E := (cell13218 ⟨28, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (83100858535573 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (1095863255041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_29 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (41533326046249 / 50000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191730536573 / 100000000000000 : ℝ))
      (E := (cell13218 ⟨29, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (41533326046249 / 50000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191730536573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_30 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (83032469515371 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191734534031 / 100000000000000 : ℝ))
      (E := (cell13218 ⟨30, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (83032469515371 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191734534031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_31 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (41499155386429 / 50000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191738562429 / 100000000000000 : ℝ))
      (E := (cell13218 ⟨31, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (41499155386429 / 50000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191738562429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_32 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (41482087916891 / 50000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (219174256439 / 10000000000000 : ℝ))
      (E := (cell13218 ⟨32, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (41482087916891 / 50000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (219174256439 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_33 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (663440517337 / 800000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191746599481 / 100000000000000 : ℝ))
      (E := (cell13218 ⟨33, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (663440517337 / 800000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191746599481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_34 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (82895977242027 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (1095875304913 / 50000000000000 : ℝ))
      (E := (cell13218 ⟨34, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (82895977242027 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (1095875304913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_35 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (10357739190973 / 12500000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191754654589 / 100000000000000 : ℝ))
      (E := (cell13218 ⟨35, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (10357739190973 / 12500000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191754654589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_36 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (10353484186731 / 12500000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (1095879337699 / 50000000000000 : ℝ))
      (E := (cell13218 ⟨36, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (10353484186731 / 12500000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (1095879337699 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_37 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (3311754284393 / 4000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191762672293 / 100000000000000 : ℝ))
      (E := (cell13218 ⟨37, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (3311754284393 / 4000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191762672293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_38 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (3310394573819 / 4000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (1095883351919 / 50000000000000 : ℝ))
      (E := (cell13218 ⟨38, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (3310394573819 / 4000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (1095883351919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13218_39 : CellCertificate 13218 (109095464340647 / 1250000000000000 : ℝ) (317811439886777 / 200000000000000000 : ℝ) (64137065754347 / 2000000000000000 : ℝ)
    (cell13218 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · norm_num [cell13218]
  · have h := gap_lower (n := 13218) (a := (82725895170711 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191770710927 / 100000000000000 : ℝ))
      (E := (cell13218 ⟨39, by decide⟩).energy) (xi := (64137065754347 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13218 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13218]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13218])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13218) (a := (82725895170711 / 100000000000000 : ℝ)) (b := (6230410523 / 4000000000000 : ℝ)) (q := (2191770710927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13218])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13218]

theorem cert13219_20 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (20843839806677 / 25000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (54789618289 / 2500000000000 : ℝ))
      (E := (cell13219 ⟨20, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (20843839806677 / 25000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (54789618289 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_21 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (83340960714597 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191588774593 / 100000000000000 : ℝ))
      (E := (cell13219 ⟨21, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (83340960714597 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191588774593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_22 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (83306586324971 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191592769003 / 100000000000000 : ℝ))
      (E := (cell13219 ⟨22, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (83306586324971 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191592769003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_23 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (16654447205037 / 20000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (1095798388213 / 50000000000000 : ℝ))
      (E := (cell13219 ⟨23, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (16654447205037 / 20000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (1095798388213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_24 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (41618954891379 / 50000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191600799941 / 100000000000000 : ℝ))
      (E := (cell13219 ⟨24, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (41618954891379 / 50000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191600799941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_25 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (83203607565379 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191604842387 / 100000000000000 : ℝ))
      (E := (cell13219 ⟨25, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (83203607565379 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191604842387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_26 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (83169329340899 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (547902211977 / 25000000000000 : ℝ))
      (E := (cell13219 ⟨26, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (83169329340899 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (547902211977 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_27 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (10391884384667 / 12500000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (1095806438651 / 50000000000000 : ℝ))
      (E := (cell13219 ⟨27, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (10391884384667 / 12500000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (1095806438651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_28 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (8310084474287 / 10000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (1095808437099 / 50000000000000 : ℝ))
      (E := (cell13219 ⟨28, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (8310084474287 / 10000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (1095808437099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_29 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (83066638305843 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191620898983 / 100000000000000 : ℝ))
      (E := (cell13219 ⟨29, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (83066638305843 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191620898983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_30 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (83032455734761 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (109581244739 / 5000000000000 : ℝ))
      (E := (cell13219 ⟨30, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (83032455734761 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (109581244739 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_31 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (82998296998287 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (547907230391 / 25000000000000 : ℝ))
      (E := (cell13219 ⟨31, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (82998296998287 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (547907230391 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_32 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (16592832413049 / 20000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191632921957 / 100000000000000 : ℝ))
      (E := (cell13219 ⟨32, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (16592832413049 / 20000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191632921957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_33 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (82930050904617 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (1095818477763 / 50000000000000 : ℝ))
      (E := (cell13219 ⟨33, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (82930050904617 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (1095818477763 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_34 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (82895963485543 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (547910241099 / 25000000000000 : ℝ))
      (E := (cell13219 ⟨34, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (82895963485543 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (547910241099 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_35 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (82861899777319 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191645007729 / 100000000000000 : ℝ))
      (E := (cell13219 ⟨35, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (82861899777319 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191645007729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_36 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (82827859749397 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (547912256789 / 25000000000000 : ℝ))
      (E := (cell13219 ⟨36, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (82827859749397 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (547912256789 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_37 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (82793843371383 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191653022713 / 100000000000000 : ℝ))
      (E := (cell13219 ⟨37, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (82793843371383 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191653022713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_38 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (82759850613037 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (273957131621 / 12500000000000 : ℝ))
      (E := (cell13219 ⟨38, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (82759850613037 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (273957131621 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13219_39 : CellCertificate 13219 (872737840392753 / 10000000000000000 : ℝ) (49654279730307 / 31250000000000000 : ℝ) (320660520099911 / 10000000000000000 : ℝ)
    (cell13219 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · norm_num [cell13219]
  · have h := gap_lower (n := 13219) (a := (82725881444271 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191661117587 / 100000000000000 : ℝ))
      (E := (cell13219 ⟨39, by decide⟩).energy) (xi := (320660520099911 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13219 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13219]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13219])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13219) (a := (82725881444271 / 100000000000000 : ℝ)) (b := (38937086657 / 25000000000000 : ℝ)) (q := (2191661117587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13219])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13219]

theorem cert13220_20 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (41687672693761 / 50000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191475106869 / 100000000000000 : ℝ))
      (E := (cell13220 ⟨20, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (41687672693761 / 50000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191475106869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_21 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (166681893763 / 200000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (87659165913 / 4000000000000 : ℝ))
      (E := (cell13220 ⟨21, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (166681893763 / 200000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (87659165913 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_22 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (83306572497959 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (1095741570101 / 50000000000000 : ℝ))
      (E := (cell13220 ⟨22, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (83306572497959 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (1095741570101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_23 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (20818055551063 / 25000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (54787178641 / 2500000000000 : ℝ))
      (E := (cell13220 ⟨23, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (20818055551063 / 25000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (54787178641 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_24 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (83237895967899 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (136968197951 / 6250000000000 : ℝ))
      (E := (cell13220 ⟨24, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (83237895967899 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (136968197951 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_25 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (20800898439147 / 25000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191495207771 / 100000000000000 : ℝ))
      (E := (cell13220 ⟨25, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (20800898439147 / 25000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191495207771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_26 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (20792328884543 / 25000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (1095749605723 / 50000000000000 : ℝ))
      (E := (cell13220 ⟨26, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (20792328884543 / 25000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (1095749605723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_27 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (20783765320167 / 25000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (3424223811 / 156250000000 : ℝ))
      (E := (cell13220 ⟨27, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (20783765320167 / 25000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (3424223811 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_28 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (16620166190451 / 20000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (273938404273 / 12500000000000 : ℝ))
      (E := (cell13220 ⟨28, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (16620166190451 / 20000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (273938404273 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_29 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (83066624521277 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191511257263 / 100000000000000 : ℝ))
      (E := (cell13220 ⟨29, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (83066624521277 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191511257263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_30 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (41516220978119 / 50000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (1095757654981 / 50000000000000 : ℝ))
      (E := (cell13220 ⟨30, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (41516220978119 / 50000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (1095757654981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_31 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (41499141612901 / 50000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (438303867031 / 20000000000000 : ℝ))
      (E := (cell13220 ⟨31, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (41499141612901 / 50000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (438303867031 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_32 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (82964148298793 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (547880833501 / 25000000000000 : ℝ))
      (E := (cell13220 ⟨32, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (82964148298793 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (547880833501 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_33 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (82930037144193 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (547881841519 / 25000000000000 : ℝ))
      (E := (cell13220 ⟨33, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (82930037144193 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (547881841519 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_34 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (82895949731143 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (1095765686747 / 50000000000000 : ℝ))
      (E := (cell13220 ⟨34, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (82895949731143 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (1095765686747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_35 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (82861886028937 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191535415423 / 100000000000000 : ℝ))
      (E := (cell13220 ⟨35, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (82861886028937 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191535415423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_36 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (82827846007027 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (547884858373 / 25000000000000 : ℝ))
      (E := (cell13220 ⟨36, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (82827846007027 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (547884858373 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_37 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (82793829635021 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191543427737 / 100000000000000 : ℝ))
      (E := (cell13220 ⟨37, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (82793829635021 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (2191543427737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_38 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (41379918441339 / 50000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (1095773728363 / 50000000000000 : ℝ))
      (E := (cell13220 ⟨38, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (41379918441339 / 50000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (1095773728363 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13220_39 : CellCertificate 13220 (17454239396081 / 200000000000000 : ℝ) (1588816721503349 / 1000000000000000000 : ℝ) (320635715288681 / 10000000000000000 : ℝ)
    (cell13220 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · norm_num [cell13220]
  · have h := gap_lower (n := 13220) (a := (82725867719911 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (273943932669 / 12500000000000 : ℝ))
      (E := (cell13220 ⟨39, by decide⟩).energy) (xi := (320635715288681 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13220 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13220]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13220])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13220) (a := (82725867719911 / 100000000000000 : ℝ)) (b := (155736432009 / 100000000000000 : ℝ)) (q := (273943932669 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13220])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13220]

theorem cert13221_20 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (83375331550431 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (136960346023 / 6250000000000 : ℝ))
      (E := (cell13221 ⟨20, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (83375331550431 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (136960346023 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_21 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (41670466525249 / 50000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (1095684758459 / 50000000000000 : ℝ))
      (E := (cell13221 ⟨21, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (41670466525249 / 50000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (1095684758459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_22 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (83306558673041 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191373565639 / 100000000000000 : ℝ))
      (E := (cell13221 ⟨22, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (83306558673041 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191373565639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_23 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (20818052096353 / 25000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (547844392279 / 25000000000000 : ℝ))
      (E := (cell13221 ⟨23, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (20818052096353 / 25000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (547844392279 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_24 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (83237882155133 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191381588777 / 100000000000000 : ℝ))
      (E := (cell13221 ⟨24, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (83237882155133 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191381588777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_25 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (8320357994989 / 10000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (273923203433 / 12500000000000 : ℝ))
      (E := (cell13221 ⟨25, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (8320357994989 / 10000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (273923203433 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_26 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (83169301737537 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (1095694814659 / 50000000000000 : ℝ))
      (E := (cell13221 ⟨26, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (83169301737537 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (1095694814659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_27 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (8313504748609 / 10000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191393655137 / 100000000000000 : ℝ))
      (E := (cell13221 ⟨27, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (8313504748609 / 10000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191393655137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_28 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (8310081716373 / 10000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (273924706069 / 12500000000000 : ℝ))
      (E := (cell13221 ⟨28, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (8310081716373 / 10000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (273924706069 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_29 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (83066610738799 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191401669949 / 100000000000000 : ℝ))
      (E := (cell13221 ⟨29, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (83066610738799 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191401669949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_30 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (41516214089901 / 50000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191405721013 / 100000000000000 : ℝ))
      (E := (cell13221 ⟨30, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (41516214089901 / 50000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191405721013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_31 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (20749567363851 / 25000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191409686031 / 100000000000000 : ℝ))
      (E := (cell13221 ⟨31, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (20749567363851 / 25000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191409686031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_32 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (82964134534427 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191413741923 / 100000000000000 : ℝ))
      (E := (cell13221 ⟨32, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (82964134534427 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191413741923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_33 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (41465011692927 / 50000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (1095708886249 / 50000000000000 : ℝ))
      (E := (cell13221 ⟨33, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (41465011692927 / 50000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (1095708886249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_34 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (3315837439153 / 4000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (1095710889233 / 50000000000000 : ℝ))
      (E := (cell13221 ⟨34, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (3315837439153 / 4000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (1095710889233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_35 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (82861872282637 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (219142581899 / 10000000000000 : ℝ))
      (E := (cell13221 ⟨35, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (82861872282637 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (219142581899 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_36 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (82827832266739 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (1095714917851 / 50000000000000 : ℝ))
      (E := (cell13221 ⟨36, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (82827832266739 / 100000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (1095714917851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_37 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (4139690795037 / 5000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (547858457159 / 25000000000000 : ℝ))
      (E := (cell13221 ⟨37, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (4139690795037 / 5000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (547858457159 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_38 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (103449778943 / 125000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191437856359 / 100000000000000 : ℝ))
      (E := (cell13221 ⟨38, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (103449778943 / 125000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (2191437856359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13221_39 : CellCertificate 13221 (109085762869777 / 1250000000000000 : ℝ) (198587063728791 / 125000000000000000 : ℝ) (160305457168549 / 5000000000000000 : ℝ)
    (cell13221 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · norm_num [cell13221]
  · have h := gap_lower (n := 13221) (a := (8272585399763 / 10000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (1095720929883 / 50000000000000 : ℝ))
      (E := (cell13221 ⟨39, by decide⟩).energy) (xi := (160305457168549 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13221 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13221]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13221])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13221) (a := (8272585399763 / 10000000000000 : ℝ)) (b := (155724519219 / 100000000000000 : ℝ)) (q := (1095720929883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13221])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13221]

theorem cert13222_20 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (20843829428859 / 25000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191255903401 / 100000000000000 : ℝ))
      (E := (cell13222 ⟨20, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (20843829428859 / 25000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191255903401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_21 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (83340919221591 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (1095629970113 / 50000000000000 : ℝ))
      (E := (cell13222 ⟨21, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (83340919221591 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (1095629970113 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_22 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (83306544850217 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (109563199347 / 5000000000000 : ℝ))
      (E := (cell13222 ⟨22, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (83306544850217 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (109563199347 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_23 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (16654438913733 / 20000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191267988457 / 100000000000000 : ℝ))
      (E := (cell13222 ⟨23, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (16654438913733 / 20000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191267988457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_24 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (41618934172229 / 50000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (438254401241 / 20000000000000 : ℝ))
      (E := (cell13222 ⟨24, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (41618934172229 / 50000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (438254401241 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_25 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (41601783072641 / 50000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (87651041721 / 4000000000000 : ℝ))
      (E := (cell13222 ⟨25, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (41601783072641 / 50000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (87651041721 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_26 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (83169287938991 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (1095640021529 / 50000000000000 : ℝ))
      (E := (cell13222 ⟨26, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (83169287938991 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (1095640021529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_27 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (83135033693601 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191284067103 / 100000000000000 : ℝ))
      (E := (cell13222 ⟨27, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (83135033693601 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191284067103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_28 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (83100803377293 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (219128805879 / 10000000000000 : ℝ))
      (E := (cell13222 ⟨28, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (83100803377293 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (219128805879 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_29 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (83066596958409 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (438258415701 / 20000000000000 : ℝ))
      (E := (cell13222 ⟨29, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (83066596958409 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (438258415701 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_30 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (83032414405453 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (1095648063967 / 50000000000000 : ℝ))
      (E := (cell13222 ⟨30, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (83032414405453 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (1095648063967 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_31 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (82998255687091 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (43826002999 / 2000000000000 : ℝ))
      (E := (cell13222 ⟨31, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (82998255687091 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (43826002999 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_32 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (16592824154429 / 20000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (1095652072857 / 50000000000000 : ℝ))
      (E := (cell13222 ⟨32, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (16592824154429 / 20000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (1095652072857 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_33 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (82930009629599 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191308174793 / 100000000000000 : ℝ))
      (E := (cell13222 ⟨33, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (82930009629599 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191308174793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_34 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (82895922228591 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (136957011207 / 6250000000000 : ℝ))
      (E := (cell13222 ⟨34, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (82895922228591 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (136957011207 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_35 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (41430929269209 / 50000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (1095658109217 / 50000000000000 : ℝ))
      (E := (cell13222 ⟨35, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (41430929269209 / 50000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (1095658109217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_36 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (82827818528533 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191320233787 / 100000000000000 : ℝ))
      (E := (cell13222 ⟨36, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (82827818528533 / 100000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191320233787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_37 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (4139690108427 / 5000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191324225411 / 100000000000000 : ℝ))
      (E := (cell13222 ⟨37, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (4139690108427 / 5000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191324225411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_38 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (413799047141 / 500000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191328251871 / 100000000000000 : ℝ))
      (E := (cell13222 ⟨38, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (413799047141 / 500000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191328251871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13222_39 : CellCertificate 13222 (872660239854397 / 10000000000000000 : ℝ) (198572039543329 / 125000000000000000 : ℝ) (160293058622109 / 5000000000000000 : ℝ)
    (cell13222 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · norm_num [cell13222]
  · have h := gap_lower (n := 13222) (a := (41362920138713 / 50000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191332312833 / 100000000000000 : ℝ))
      (E := (cell13222 ⟨39, by decide⟩).energy) (xi := (160293058622109 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13222 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13222]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13222])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13222) (a := (41362920138713 / 50000000000000 : ℝ)) (b := (155712608257 / 100000000000000 : ℝ)) (q := (2191332312833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13222])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13222]

theorem cert13223_20 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (83375303882537 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (1095573191477 / 50000000000000 : ℝ))
      (E := (cell13223 ⟨20, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (83375303882537 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (1095573191477 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_21 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (83340905394779 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (1095575179699 / 50000000000000 : ℝ))
      (E := (cell13223 ⟨21, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (83340905394779 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (1095575179699 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_22 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (41653265514743 / 50000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191154404107 / 100000000000000 : ℝ))
      (E := (cell13223 ⟨22, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (41653265514743 / 50000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191154404107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_23 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (83272180754011 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (438231680733 / 20000000000000 : ℝ))
      (E := (cell13223 ⟨23, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (83272180754011 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (438231680733 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_24 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (665902836287 / 800000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (4382324839 / 200000000000 : ℝ))
      (E := (cell13223 ⟨24, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (665902836287 / 800000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (4382324839 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_25 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (16640710468553 / 20000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (1095583227227 / 50000000000000 : ℝ))
      (E := (cell13223 ⟨25, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (16640710468553 / 20000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (1095583227227 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_26 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (16633854828507 / 20000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191170452667 / 100000000000000 : ℝ))
      (E := (cell13223 ⟨26, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (16633854828507 / 20000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191170452667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_27 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (83135019903201 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (1095587237469 / 50000000000000 : ℝ))
      (E := (cell13223 ⟨27, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (83135019903201 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (1095587237469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_28 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (83100789592943 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (438235704683 / 20000000000000 : ℝ))
      (E := (cell13223 ⟨28, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (83100789592943 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (438235704683 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_29 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (16613316636021 / 20000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (68474454421 / 3125000000000 : ℝ))
      (E := (cell13223 ⟨29, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (16613316636021 / 20000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (68474454421 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_30 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (8303240063319 / 10000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (273898316341 / 12500000000000 : ℝ))
      (E := (cell13223 ⟨30, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (8303240063319 / 10000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (273898316341 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_31 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (82998241920863 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191190551157 / 100000000000000 : ℝ))
      (E := (cell13223 ⟨31, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (82998241920863 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191190551157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_32 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (20741026752987 / 25000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (547798650997 / 25000000000000 : ℝ))
      (E := (cell13223 ⟨32, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (20741026752987 / 25000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (547798650997 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_33 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (41464997937713 / 50000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191198631597 / 100000000000000 : ℝ))
      (E := (cell13223 ⟨33, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (41464997937713 / 50000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191198631597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_34 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (82895908480439 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191202634691 / 100000000000000 : ℝ))
      (E := (cell13223 ⟨34, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (82895908480439 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191202634691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_35 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (41430922398141 / 50000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191206672433 / 100000000000000 : ℝ))
      (E := (cell13223 ⟨35, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (41430922398141 / 50000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191206672433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_36 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (41413902396203 / 50000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (438242137291 / 20000000000000 : ℝ))
      (E := (cell13223 ⟨36, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (41413902396203 / 50000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (438242137291 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_37 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (82793788438419 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (273901834599 / 12500000000000 : ℝ))
      (E := (cell13223 ⟨37, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (82793788438419 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (273901834599 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_38 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (82759795704079 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (547804675503 / 25000000000000 : ℝ))
      (E := (cell13223 ⟨38, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (82759795704079 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (547804675503 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13223_39 : CellCertificate 13223 (872634380491743 / 10000000000000000 : ℝ) (1588456141048133 / 1000000000000000000 : ℝ) (160280662004547 / 5000000000000000 : ℝ)
    (cell13223 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · norm_num [cell13223]
  · have h := gap_lower (n := 13223) (a := (82725826559301 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191222703007 / 100000000000000 : ℝ))
      (E := (cell13223 ⟨39, by decide⟩).energy) (xi := (160280662004547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13223 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13223]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13223])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13223) (a := (82725826559301 / 100000000000000 : ℝ)) (b := (77850349561 / 50000000000000 : ℝ)) (q := (2191222703007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13223])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13223]

theorem cert13224_20 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (20843822512933 / 25000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (547759200011 / 25000000000000 : ℝ))
      (E := (cell13224 ⟨20, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (20843822512933 / 25000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (547759200011 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_21 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (4167044578503 / 5000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (547760208197 / 25000000000000 : ℝ))
      (E := (cell13224 ⟨21, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (4167044578503 / 5000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (547760208197 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_22 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (2603328662839 / 3125000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (438208975103 / 20000000000000 : ℝ))
      (E := (cell13224 ⟨22, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (2603328662839 / 3125000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (438208975103 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_23 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (10409020867681 / 12500000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191048873139 / 100000000000000 : ℝ))
      (E := (cell13224 ⟨23, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (10409020867681 / 12500000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191048873139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_24 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (83237840729383 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (547763221771 / 25000000000000 : ℝ))
      (E := (cell13224 ⟨24, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (83237840729383 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (547763221771 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_25 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (83203538542339 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (547764230049 / 25000000000000 : ℝ))
      (E := (cell13224 ⟨25, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (83203538542339 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (547764230049 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_26 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (10396157543521 / 12500000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (438212183323 / 20000000000000 : ℝ))
      (E := (cell13224 ⟨26, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (10396157543521 / 12500000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (438212183323 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_27 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (83135006114889 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191064937137 / 100000000000000 : ℝ))
      (E := (cell13224 ⟨27, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (83135006114889 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191064937137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_28 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (83100775810681 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191068983911 / 100000000000000 : ℝ))
      (E := (cell13224 ⟨28, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (83100775810681 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191068983911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_29 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (83066569403887 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191073000313 / 100000000000000 : ℝ))
      (E := (cell13224 ⟨29, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (83066569403887 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191073000313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_30 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (20758096715753 / 25000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191076987959 / 100000000000000 : ℝ))
      (E := (cell13224 ⟨30, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (20758096715753 / 25000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191076987959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_31 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (82998228156719 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (273885125853 / 12500000000000 : ℝ))
      (E := (cell13224 ⟨31, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (82998228156719 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (273885125853 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_32 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (41482046626917 / 50000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (1095542529069 / 50000000000000 : ℝ))
      (E := (cell13224 ⟨32, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (41482046626917 / 50000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (1095542529069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_33 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (82929982123337 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (547772271069 / 25000000000000 : ℝ))
      (E := (cell13224 ⟨33, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (82929982123337 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (547772271069 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_34 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (82895894734369 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (438218617189 / 20000000000000 : ℝ))
      (E := (cell13224 ⟨34, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (82895894734369 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (438218617189 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_35 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (41430915528113 / 50000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191097122311 / 100000000000000 : ℝ))
      (E := (cell13224 ⟨35, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (41430915528113 / 50000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191097122311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_36 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (2070694776459 / 2500000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (438220227 / 20000000000 : ℝ))
      (E := (cell13224 ⟨36, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (2070694776459 / 2500000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (438220227 / 20000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_37 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (10349221838797 / 12500000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191105124053 / 100000000000000 : ℝ))
      (E := (cell13224 ⟨37, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (10349221838797 / 12500000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191105124053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_38 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (20689945495509 / 25000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191109148033 / 100000000000000 : ℝ))
      (E := (cell13224 ⟨38, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (20689945495509 / 25000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (2191109148033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

theorem cert13224_39 : CellCertificate 13224 (436304262434701 / 5000000000000000 : ℝ) (99270998995669 / 62500000000000000 : ℝ) (160268267315391 / 5000000000000000 : ℝ)
    (cell13224 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · norm_num [cell13224]
  · have h := gap_lower (n := 13224) (a := (82725812843253 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (136944575413 / 6250000000000 : ℝ))
      (E := (cell13224 ⟨39, by decide⟩).energy) (xi := (160268267315391 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13224 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13224]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13224])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13224) (a := (82725812843253 / 100000000000000 : ℝ)) (b := (77844395907 / 50000000000000 : ℝ)) (q := (136944575413 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13224])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13224]

end BstLean.Part268
