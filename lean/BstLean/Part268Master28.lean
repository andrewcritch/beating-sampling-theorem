import BstLean.Part261Checker
import BstLean.Part268Scalar28
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp13050 : ℝ := (2346874403 / 10000000000)
noncomputable def tm13050 : ℝ := (-((6130017561 / 10000000000)))
noncomputable def ep13050 : ℝ := (52319900282383693 / 100000000000000000000)
noncomputable def em13050 : ℝ := (25442602483558629 / 50000000000000000000)
noncomputable def bp13050 : ℝ := (21296753261764670661 / 50000000000000000000)
noncomputable def bm13050 : ℝ := (21801049250682462617 / 50000000000000000000)

theorem positive13050 :
    Eplus aL (agent13050.root+dsL) scalar13050.worldRadius world13050.frame
      agent13050.frame tp13050 ≤ -ep13050 := by
  apply positive_check (eT := (115687295666459815327 / 100000000000000000000)) (y := (1904586276103752523 / 5000000000000000000)) (u := (146362649294802296247 / 100000000000000000000))
  · norm_num [world13050, agent13050, scalar13050, tp13050, tm13050, ep13050, em13050, dsL]
  · norm_num [world13050, agent13050, scalar13050, tp13050, tm13050, ep13050, em13050, dsL]
  · norm_num [world13050, agent13050, scalar13050, tp13050, tm13050, ep13050, em13050, dsL]
  · norm_num [world13050, agent13050, scalar13050, tp13050, tm13050, ep13050, em13050, dsL]
  · norm_num [world13050, agent13050, scalar13050, tp13050, tm13050, ep13050, em13050, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13050, agent13050, tp13050, tm13050, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13050, agent13050, scalar13050, tp13050, tm13050, ep13050, em13050, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13050, agent13050, tp13050, tm13050, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13050, agent13050, scalar13050, tp13050, tm13050, ep13050, em13050, dsL]

theorem negative13050 :
    Eminus aL (agent13050.root+dsL) scalar13050.worldRadius world13050.frame
      agent13050.frame tm13050 ≤ -em13050 := by
  apply negative_check (lo := (34171837501076158447 / 50000000000000000000)) (hi := (13668735000430463379 / 20000000000000000000))
    (y := (-((71622100990904177613 / 100000000000000000000)))) (u := (12214879197294450347 / 25000000000000000000))
  · norm_num [world13050, agent13050, scalar13050, tp13050, tm13050, ep13050, em13050, dsL]
  · norm_num [world13050, agent13050, scalar13050, tp13050, tm13050, ep13050, em13050, dsL]
  · norm_num [world13050, agent13050, scalar13050, tp13050, tm13050, ep13050, em13050, dsL]
  · norm_num [world13050, agent13050, scalar13050, tp13050, tm13050, ep13050, em13050, dsL]
  · norm_num [world13050, agent13050, scalar13050, tp13050, tm13050, ep13050, em13050, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13050, agent13050, tp13050, tm13050, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13050, agent13050, tp13050, tm13050, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13050, agent13050, scalar13050, tp13050, tm13050, ep13050, em13050, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13050, agent13050, tp13050, tm13050, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13050, agent13050, scalar13050, tp13050, tm13050, ep13050, em13050, dsL]

theorem tails13050 :
    exp (-((13050:ℝ)*ep13050)) ≤ scalar13050.upperTail ∧
    exp (-((13050:ℝ)*em13050)) ≤ scalar13050.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13050:ℝ)) (by norm_num [ep13050]) ?_)
      (show bp13050^8 ≤ scalar13050.upperTail by norm_num [bp13050, scalar13050])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13050, bp13050, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13050:ℝ)) (by norm_num [em13050]) ?_)
      (show bm13050^8 ≤ scalar13050.lowerTail by norm_num [bm13050, scalar13050])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13050, bm13050, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13050 :
    agent13050.root+dsL+scalar13050.worldRadius < √(1/100/aL) ∧
    2*(agent13050.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13050, agent13050, scalar13050, tp13050, tm13050, ep13050, em13050, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13050, agent13050, scalar13050, tp13050, tm13050, ep13050, em13050, dsL]

noncomputable def master13050 : MasterCertificate 13050 world13050 agent13050 :=
  master scalar13050 dsL tp13050 tm13050 ep13050 em13050
    (by norm_num [dsL]) (by norm_num [tp13050]) (by norm_num [tm13050])
    (by norm_num [ep13050]) (by norm_num [em13050])
    positive13050 negative13050 tails13050.1 tails13050.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13050.1 tailGuards13050.2

theorem preserves13050 : master13050.toScalarCertificate = scalar13050 := rfl

noncomputable def tp13051 : ℝ := (146684281 / 625000000)
noncomputable def tm13051 : ℝ := (-((6130174807 / 10000000000)))
noncomputable def ep13051 : ℝ := (10464425405154399 / 20000000000000000000)
noncomputable def em13051 : ℝ := (10177418921770997 / 20000000000000000000)
noncomputable def bp13051 : ℝ := (42589173859385368807 / 100000000000000000000)
noncomputable def bm13051 : ℝ := (5449747648813011313 / 12500000000000000000)

theorem positive13051 :
    Eplus aL (agent13051.root+dsL) scalar13051.worldRadius world13051.frame
      agent13051.frame tp13051 ≤ -ep13051 := by
  apply positive_check (eT := (2313749445098036743 / 2000000000000000000)) (y := (38092394528318124429 / 100000000000000000000)) (u := (146363628473338986051 / 100000000000000000000))
  · norm_num [world13051, agent13051, scalar13051, tp13051, tm13051, ep13051, em13051, dsL]
  · norm_num [world13051, agent13051, scalar13051, tp13051, tm13051, ep13051, em13051, dsL]
  · norm_num [world13051, agent13051, scalar13051, tp13051, tm13051, ep13051, em13051, dsL]
  · norm_num [world13051, agent13051, scalar13051, tp13051, tm13051, ep13051, em13051, dsL]
  · norm_num [world13051, agent13051, scalar13051, tp13051, tm13051, ep13051, em13051, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13051, agent13051, tp13051, tm13051, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13051, agent13051, scalar13051, tp13051, tm13051, ep13051, em13051, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13051, agent13051, tp13051, tm13051, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13051, agent13051, scalar13051, tp13051, tm13051, ep13051, em13051, dsL]

theorem negative13051 :
    Eminus aL (agent13051.root+dsL) scalar13051.worldRadius world13051.frame
      agent13051.frame tm13051 ≤ -em13051 := by
  apply negative_check (lo := (34171778243023958899 / 50000000000000000000)) (hi := (68343556486047917799 / 100000000000000000000))
    (y := (-((71622033055499157593 / 100000000000000000000)))) (u := (48859549982099697813 / 100000000000000000000))
  · norm_num [world13051, agent13051, scalar13051, tp13051, tm13051, ep13051, em13051, dsL]
  · norm_num [world13051, agent13051, scalar13051, tp13051, tm13051, ep13051, em13051, dsL]
  · norm_num [world13051, agent13051, scalar13051, tp13051, tm13051, ep13051, em13051, dsL]
  · norm_num [world13051, agent13051, scalar13051, tp13051, tm13051, ep13051, em13051, dsL]
  · norm_num [world13051, agent13051, scalar13051, tp13051, tm13051, ep13051, em13051, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13051, agent13051, tp13051, tm13051, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13051, agent13051, tp13051, tm13051, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13051, agent13051, scalar13051, tp13051, tm13051, ep13051, em13051, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13051, agent13051, tp13051, tm13051, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13051, agent13051, scalar13051, tp13051, tm13051, ep13051, em13051, dsL]

theorem tails13051 :
    exp (-((13051:ℝ)*ep13051)) ≤ scalar13051.upperTail ∧
    exp (-((13051:ℝ)*em13051)) ≤ scalar13051.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13051:ℝ)) (by norm_num [ep13051]) ?_)
      (show bp13051^8 ≤ scalar13051.upperTail by norm_num [bp13051, scalar13051])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13051, bp13051, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13051:ℝ)) (by norm_num [em13051]) ?_)
      (show bm13051^8 ≤ scalar13051.lowerTail by norm_num [bm13051, scalar13051])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13051, bm13051, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13051 :
    agent13051.root+dsL+scalar13051.worldRadius < √(1/100/aL) ∧
    2*(agent13051.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13051, agent13051, scalar13051, tp13051, tm13051, ep13051, em13051, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13051, agent13051, scalar13051, tp13051, tm13051, ep13051, em13051, dsL]

noncomputable def master13051 : MasterCertificate 13051 world13051 agent13051 :=
  master scalar13051 dsL tp13051 tm13051 ep13051 em13051
    (by norm_num [dsL]) (by norm_num [tp13051]) (by norm_num [tm13051])
    (by norm_num [ep13051]) (by norm_num [em13051])
    positive13051 negative13051 tails13051.1 tails13051.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13051.1 tailGuards13051.2

theorem preserves13051 : master13051.toScalarCertificate = scalar13051 := rfl

noncomputable def tp13052 : ℝ := (2347022523 / 10000000000)
noncomputable def tm13052 : ℝ := (-((766291493 / 1250000000)))
noncomputable def ep13052 : ℝ := (52324352403876177 / 100000000000000000000)
noncomputable def em13052 : ℝ := (50888982952968043 / 100000000000000000000)
noncomputable def bp13052 : ℝ := (13307763233581977 / 31250000000000000)
noncomputable def bm13052 : ℝ := (2724616561588142347 / 6250000000000000000)

theorem positive13052 :
    Eplus aL (agent13052.root+dsL) scalar13052.worldRadius world13052.frame
      agent13052.frame tp13052 ≤ -ep13052 := by
  apply positive_check (eT := (2313752968045748687 / 2000000000000000000)) (y := (38093062853672686037 / 100000000000000000000)) (u := (73182303330923333497 / 50000000000000000000))
  · norm_num [world13052, agent13052, scalar13052, tp13052, tm13052, ep13052, em13052, dsL]
  · norm_num [world13052, agent13052, scalar13052, tp13052, tm13052, ep13052, em13052, dsL]
  · norm_num [world13052, agent13052, scalar13052, tp13052, tm13052, ep13052, em13052, dsL]
  · norm_num [world13052, agent13052, scalar13052, tp13052, tm13052, ep13052, em13052, dsL]
  · norm_num [world13052, agent13052, scalar13052, tp13052, tm13052, ep13052, em13052, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13052, agent13052, tp13052, tm13052, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13052, agent13052, scalar13052, tp13052, tm13052, ep13052, em13052, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13052, agent13052, tp13052, tm13052, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13052, agent13052, scalar13052, tp13052, tm13052, ep13052, em13052, dsL]

theorem negative13052 :
    Eminus aL (agent13052.root+dsL) scalar13052.worldRadius world13052.frame
      agent13052.frame tm13052 ≤ -em13052 := by
  apply negative_check (lo := (34171719187825871751 / 50000000000000000000)) (hi := (68343438375651743503 / 100000000000000000000))
    (y := (-((2864878588049263989 / 4000000000000000000)))) (u := (6107447922462329311 / 12500000000000000000))
  · norm_num [world13052, agent13052, scalar13052, tp13052, tm13052, ep13052, em13052, dsL]
  · norm_num [world13052, agent13052, scalar13052, tp13052, tm13052, ep13052, em13052, dsL]
  · norm_num [world13052, agent13052, scalar13052, tp13052, tm13052, ep13052, em13052, dsL]
  · norm_num [world13052, agent13052, scalar13052, tp13052, tm13052, ep13052, em13052, dsL]
  · norm_num [world13052, agent13052, scalar13052, tp13052, tm13052, ep13052, em13052, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13052, agent13052, tp13052, tm13052, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13052, agent13052, tp13052, tm13052, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13052, agent13052, scalar13052, tp13052, tm13052, ep13052, em13052, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13052, agent13052, tp13052, tm13052, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13052, agent13052, scalar13052, tp13052, tm13052, ep13052, em13052, dsL]

theorem tails13052 :
    exp (-((13052:ℝ)*ep13052)) ≤ scalar13052.upperTail ∧
    exp (-((13052:ℝ)*em13052)) ≤ scalar13052.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13052:ℝ)) (by norm_num [ep13052]) ?_)
      (show bp13052^8 ≤ scalar13052.upperTail by norm_num [bp13052, scalar13052])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13052, bp13052, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13052:ℝ)) (by norm_num [em13052]) ?_)
      (show bm13052^8 ≤ scalar13052.lowerTail by norm_num [bm13052, scalar13052])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13052, bm13052, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13052 :
    agent13052.root+dsL+scalar13052.worldRadius < √(1/100/aL) ∧
    2*(agent13052.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13052, agent13052, scalar13052, tp13052, tm13052, ep13052, em13052, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13052, agent13052, scalar13052, tp13052, tm13052, ep13052, em13052, dsL]

noncomputable def master13052 : MasterCertificate 13052 world13052 agent13052 :=
  master scalar13052 dsL tp13052 tm13052 ep13052 em13052
    (by norm_num [dsL]) (by norm_num [tp13052]) (by norm_num [tm13052])
    (by norm_num [ep13052]) (by norm_num [em13052])
    positive13052 negative13052 tails13052.1 tails13052.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13052.1 tailGuards13052.2

theorem preserves13052 : master13052.toScalarCertificate = scalar13052 := rfl

noncomputable def tp13053 : ℝ := (2347096583 / 10000000000)
noncomputable def tm13053 : ℝ := (-((3065244479 / 5000000000)))
noncomputable def ep13053 : ℝ := (52326576777624001 / 100000000000000000000)
noncomputable def em13053 : ℝ := (12722717594673657 / 25000000000000000000)
noncomputable def bp13053 : ℝ := (42580511736960193861 / 100000000000000000000)
noncomputable def bm13053 : ℝ := (10897437404083386263 / 25000000000000000000)

theorem positive13053 :
    Eplus aL (agent13053.root+dsL) scalar13053.worldRadius world13053.frame
      agent13053.frame tp13053 ≤ -ep13053 := by
  apply positive_check (eT := (115687824819743108147 / 100000000000000000000)) (y := (38093732124147230787 / 100000000000000000000)) (u := (146365586240222249057 / 100000000000000000000))
  · norm_num [world13053, agent13053, scalar13053, tp13053, tm13053, ep13053, em13053, dsL]
  · norm_num [world13053, agent13053, scalar13053, tp13053, tm13053, ep13053, em13053, dsL]
  · norm_num [world13053, agent13053, scalar13053, tp13053, tm13053, ep13053, em13053, dsL]
  · norm_num [world13053, agent13053, scalar13053, tp13053, tm13053, ep13053, em13053, dsL]
  · norm_num [world13053, agent13053, scalar13053, tp13053, tm13053, ep13053, em13053, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13053, agent13053, tp13053, tm13053, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13053, agent13053, scalar13053, tp13053, tm13053, ep13053, em13053, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13053, agent13053, tp13053, tm13053, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13053, agent13053, scalar13053, tp13053, tm13053, ep13053, em13053, dsL]

theorem negative13053 :
    Eminus aL (agent13053.root+dsL) scalar13053.worldRadius world13053.frame
      agent13053.frame tm13053 ≤ -em13053 := by
  apply negative_check (lo := (13668664146066307299 / 20000000000000000000)) (hi := (4271457545645721031 / 6250000000000000000))
    (y := (-((71621896042657909627 / 100000000000000000000)))) (u := (48859616926003210119 / 100000000000000000000))
  · norm_num [world13053, agent13053, scalar13053, tp13053, tm13053, ep13053, em13053, dsL]
  · norm_num [world13053, agent13053, scalar13053, tp13053, tm13053, ep13053, em13053, dsL]
  · norm_num [world13053, agent13053, scalar13053, tp13053, tm13053, ep13053, em13053, dsL]
  · norm_num [world13053, agent13053, scalar13053, tp13053, tm13053, ep13053, em13053, dsL]
  · norm_num [world13053, agent13053, scalar13053, tp13053, tm13053, ep13053, em13053, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13053, agent13053, tp13053, tm13053, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13053, agent13053, tp13053, tm13053, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13053, agent13053, scalar13053, tp13053, tm13053, ep13053, em13053, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13053, agent13053, tp13053, tm13053, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13053, agent13053, scalar13053, tp13053, tm13053, ep13053, em13053, dsL]

theorem tails13053 :
    exp (-((13053:ℝ)*ep13053)) ≤ scalar13053.upperTail ∧
    exp (-((13053:ℝ)*em13053)) ≤ scalar13053.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13053:ℝ)) (by norm_num [ep13053]) ?_)
      (show bp13053^8 ≤ scalar13053.upperTail by norm_num [bp13053, scalar13053])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13053, bp13053, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13053:ℝ)) (by norm_num [em13053]) ?_)
      (show bm13053^8 ≤ scalar13053.lowerTail by norm_num [bm13053, scalar13053])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13053, bm13053, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13053 :
    agent13053.root+dsL+scalar13053.worldRadius < √(1/100/aL) ∧
    2*(agent13053.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13053, agent13053, scalar13053, tp13053, tm13053, ep13053, em13053, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13053, agent13053, scalar13053, tp13053, tm13053, ep13053, em13053, dsL]

noncomputable def master13053 : MasterCertificate 13053 world13053 agent13053 :=
  master scalar13053 dsL tp13053 tm13053 ep13053 em13053
    (by norm_num [dsL]) (by norm_num [tp13053]) (by norm_num [tm13053])
    (by norm_num [ep13053]) (by norm_num [em13053])
    positive13053 negative13053 tails13053.1 tails13053.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13053.1 tailGuards13053.2

theorem preserves13053 : master13053.toScalarCertificate = scalar13053 := rfl

noncomputable def tp13054 : ℝ := (1173585259 / 5000000000)
noncomputable def tm13054 : ℝ := (-((613064593 / 1000000000)))
noncomputable def ep13054 : ℝ := (5232879944271467 / 10000000000000000000)
noncomputable def em13054 : ℝ := (12723189051548319 / 25000000000000000000)
noncomputable def bp13054 : ℝ := (42576182517157635431 / 100000000000000000000)
noncomputable def bm13054 : ℝ := (4358563556676970211 / 10000000000000000000)

theorem positive13054 :
    Eplus aL (agent13054.root+dsL) scalar13054.worldRadius world13054.frame
      agent13054.frame tp13054 ≤ -ep13054 := by
  apply positive_check (eT := (115688000372379199877 / 100000000000000000000)) (y := (38094399581516195099 / 100000000000000000000)) (u := (4573955099105422909 / 3125000000000000000))
  · norm_num [world13054, agent13054, scalar13054, tp13054, tm13054, ep13054, em13054, dsL]
  · norm_num [world13054, agent13054, scalar13054, tp13054, tm13054, ep13054, em13054, dsL]
  · norm_num [world13054, agent13054, scalar13054, tp13054, tm13054, ep13054, em13054, dsL]
  · norm_num [world13054, agent13054, scalar13054, tp13054, tm13054, ep13054, em13054, dsL]
  · norm_num [world13054, agent13054, scalar13054, tp13054, tm13054, ep13054, em13054, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13054, agent13054, tp13054, tm13054, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13054, agent13054, scalar13054, tp13054, tm13054, ep13054, em13054, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13054, agent13054, tp13054, tm13054, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13054, agent13054, scalar13054, tp13054, tm13054, ep13054, em13054, dsL]

theorem negative13054 :
    Eminus aL (agent13054.root+dsL) scalar13054.worldRadius world13054.frame
      agent13054.frame tm13054 ≤ -em13054 := by
  apply negative_check (lo := (68343203206390872419 / 100000000000000000000)) (hi := (3417160160319543621 / 5000000000000000000))
    (y := (-((71621827193840341053 / 100000000000000000000)))) (u := (48859650565283312329 / 100000000000000000000))
  · norm_num [world13054, agent13054, scalar13054, tp13054, tm13054, ep13054, em13054, dsL]
  · norm_num [world13054, agent13054, scalar13054, tp13054, tm13054, ep13054, em13054, dsL]
  · norm_num [world13054, agent13054, scalar13054, tp13054, tm13054, ep13054, em13054, dsL]
  · norm_num [world13054, agent13054, scalar13054, tp13054, tm13054, ep13054, em13054, dsL]
  · norm_num [world13054, agent13054, scalar13054, tp13054, tm13054, ep13054, em13054, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13054, agent13054, tp13054, tm13054, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13054, agent13054, tp13054, tm13054, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13054, agent13054, scalar13054, tp13054, tm13054, ep13054, em13054, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13054, agent13054, tp13054, tm13054, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13054, agent13054, scalar13054, tp13054, tm13054, ep13054, em13054, dsL]

theorem tails13054 :
    exp (-((13054:ℝ)*ep13054)) ≤ scalar13054.upperTail ∧
    exp (-((13054:ℝ)*em13054)) ≤ scalar13054.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13054:ℝ)) (by norm_num [ep13054]) ?_)
      (show bp13054^8 ≤ scalar13054.upperTail by norm_num [bp13054, scalar13054])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13054, bp13054, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13054:ℝ)) (by norm_num [em13054]) ?_)
      (show bm13054^8 ≤ scalar13054.lowerTail by norm_num [bm13054, scalar13054])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13054, bm13054, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13054 :
    agent13054.root+dsL+scalar13054.worldRadius < √(1/100/aL) ∧
    2*(agent13054.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13054, agent13054, scalar13054, tp13054, tm13054, ep13054, em13054, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13054, agent13054, scalar13054, tp13054, tm13054, ep13054, em13054, dsL]

noncomputable def master13054 : MasterCertificate 13054 world13054 agent13054 :=
  master scalar13054 dsL tp13054 tm13054 ep13054 em13054
    (by norm_num [dsL]) (by norm_num [tp13054]) (by norm_num [tm13054])
    (by norm_num [ep13054]) (by norm_num [em13054])
    positive13054 negative13054 tails13054.1 tails13054.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13054.1 tailGuards13054.2

theorem preserves13054 : master13054.toScalarCertificate = scalar13054 := rfl

noncomputable def tp13055 : ℝ := (469448897 / 2000000000)
noncomputable def tm13055 : ℝ := (-((1532700701 / 2500000000)))
noncomputable def ep13055 : ℝ := (26165511104086081 / 50000000000000000000)
noncomputable def em13055 : ℝ := (50894642155509223 / 100000000000000000000)
noncomputable def bp13055 : ℝ := (42571853431228656003 / 100000000000000000000)
noncomputable def bm13055 : ℝ := (5447690201673803763 / 12500000000000000000)

theorem positive13055 :
    Eplus aL (agent13055.root+dsL) scalar13055.worldRadius world13055.frame
      agent13055.frame tp13055 ≤ -ep13055 := by
  apply positive_check (eT := (115688176187875903981 / 100000000000000000000)) (y := (3809506771545025893 / 10000000000000000000)) (u := (146367541099317134591 / 100000000000000000000))
  · norm_num [world13055, agent13055, scalar13055, tp13055, tm13055, ep13055, em13055, dsL]
  · norm_num [world13055, agent13055, scalar13055, tp13055, tm13055, ep13055, em13055, dsL]
  · norm_num [world13055, agent13055, scalar13055, tp13055, tm13055, ep13055, em13055, dsL]
  · norm_num [world13055, agent13055, scalar13055, tp13055, tm13055, ep13055, em13055, dsL]
  · norm_num [world13055, agent13055, scalar13055, tp13055, tm13055, ep13055, em13055, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13055, agent13055, tp13055, tm13055, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13055, agent13055, scalar13055, tp13055, tm13055, ep13055, em13055, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13055, agent13055, tp13055, tm13055, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13055, agent13055, scalar13055, tp13055, tm13055, ep13055, em13055, dsL]

theorem negative13055 :
    Eminus aL (agent13055.root+dsL) scalar13055.worldRadius world13055.frame
      agent13055.frame tm13055 ≤ -em13055 := by
  apply negative_check (lo := (68343086041465026969 / 100000000000000000000)) (hi := (6834308604146502697 / 10000000000000000000))
    (y := (-((17905439562445394219 / 25000000000000000000)))) (u := (2442984212556056111 / 5000000000000000000))
  · norm_num [world13055, agent13055, scalar13055, tp13055, tm13055, ep13055, em13055, dsL]
  · norm_num [world13055, agent13055, scalar13055, tp13055, tm13055, ep13055, em13055, dsL]
  · norm_num [world13055, agent13055, scalar13055, tp13055, tm13055, ep13055, em13055, dsL]
  · norm_num [world13055, agent13055, scalar13055, tp13055, tm13055, ep13055, em13055, dsL]
  · norm_num [world13055, agent13055, scalar13055, tp13055, tm13055, ep13055, em13055, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13055, agent13055, tp13055, tm13055, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13055, agent13055, tp13055, tm13055, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13055, agent13055, scalar13055, tp13055, tm13055, ep13055, em13055, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13055, agent13055, tp13055, tm13055, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13055, agent13055, scalar13055, tp13055, tm13055, ep13055, em13055, dsL]

theorem tails13055 :
    exp (-((13055:ℝ)*ep13055)) ≤ scalar13055.upperTail ∧
    exp (-((13055:ℝ)*em13055)) ≤ scalar13055.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13055:ℝ)) (by norm_num [ep13055]) ?_)
      (show bp13055^8 ≤ scalar13055.upperTail by norm_num [bp13055, scalar13055])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13055, bp13055, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13055:ℝ)) (by norm_num [em13055]) ?_)
      (show bm13055^8 ≤ scalar13055.lowerTail by norm_num [bm13055, scalar13055])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13055, bm13055, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13055 :
    agent13055.root+dsL+scalar13055.worldRadius < √(1/100/aL) ∧
    2*(agent13055.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13055, agent13055, scalar13055, tp13055, tm13055, ep13055, em13055, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13055, agent13055, scalar13055, tp13055, tm13055, ep13055, em13055, dsL]

noncomputable def master13055 : MasterCertificate 13055 world13055 agent13055 :=
  master scalar13055 dsL tp13055 tm13055 ep13055 em13055
    (by norm_num [dsL]) (by norm_num [tp13055]) (by norm_num [tm13055])
    (by norm_num [ep13055]) (by norm_num [em13055])
    positive13055 negative13055 tails13055.1 tails13055.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13055.1 tailGuards13055.2

theorem preserves13055 : master13055.toScalarCertificate = scalar13055 := rfl

noncomputable def tp13056 : ℝ := (2347318407 / 10000000000)
noncomputable def tm13056 : ℝ := (-((1532739887 / 2500000000)))
noncomputable def ep13056 : ℝ := (10466648499783717 / 20000000000000000000)
noncomputable def em13056 : ℝ := (50896525818467819 / 100000000000000000000)
noncomputable def bp13056 : ℝ := (21283763134058854207 / 50000000000000000000)
noncomputable def bm13056 : ℝ := (1089435236721887587 / 2500000000000000000)

theorem positive13056 :
    Eplus aL (agent13056.root+dsL) scalar13056.worldRadius world13056.frame
      agent13056.frame tp13056 ≤ -ep13056 := by
  apply positive_check (eT := (57844175856606073583 / 50000000000000000000)) (y := (38095735479778110597 / 100000000000000000000)) (u := (146368518492807488363 / 100000000000000000000))
  · norm_num [world13056, agent13056, scalar13056, tp13056, tm13056, ep13056, em13056, dsL]
  · norm_num [world13056, agent13056, scalar13056, tp13056, tm13056, ep13056, em13056, dsL]
  · norm_num [world13056, agent13056, scalar13056, tp13056, tm13056, ep13056, em13056, dsL]
  · norm_num [world13056, agent13056, scalar13056, tp13056, tm13056, ep13056, em13056, dsL]
  · norm_num [world13056, agent13056, scalar13056, tp13056, tm13056, ep13056, em13056, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13056, agent13056, tp13056, tm13056, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13056, agent13056, scalar13056, tp13056, tm13056, ep13056, em13056, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13056, agent13056, tp13056, tm13056, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13056, agent13056, scalar13056, tp13056, tm13056, ep13056, em13056, dsL]

theorem negative13056 :
    Eminus aL (agent13056.root+dsL) scalar13056.worldRadius world13056.frame
      agent13056.frame tm13056 ≤ -em13056 := by
  apply negative_check (lo := (68342969371252505293 / 100000000000000000000)) (hi := (34171484685626252647 / 50000000000000000000))
    (y := (-((17905422034842230879 / 25000000000000000000)))) (u := (12214929626714845057 / 25000000000000000000))
  · norm_num [world13056, agent13056, scalar13056, tp13056, tm13056, ep13056, em13056, dsL]
  · norm_num [world13056, agent13056, scalar13056, tp13056, tm13056, ep13056, em13056, dsL]
  · norm_num [world13056, agent13056, scalar13056, tp13056, tm13056, ep13056, em13056, dsL]
  · norm_num [world13056, agent13056, scalar13056, tp13056, tm13056, ep13056, em13056, dsL]
  · norm_num [world13056, agent13056, scalar13056, tp13056, tm13056, ep13056, em13056, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13056, agent13056, tp13056, tm13056, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13056, agent13056, tp13056, tm13056, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13056, agent13056, scalar13056, tp13056, tm13056, ep13056, em13056, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13056, agent13056, tp13056, tm13056, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13056, agent13056, scalar13056, tp13056, tm13056, ep13056, em13056, dsL]

theorem tails13056 :
    exp (-((13056:ℝ)*ep13056)) ≤ scalar13056.upperTail ∧
    exp (-((13056:ℝ)*em13056)) ≤ scalar13056.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13056:ℝ)) (by norm_num [ep13056]) ?_)
      (show bp13056^8 ≤ scalar13056.upperTail by norm_num [bp13056, scalar13056])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13056, bp13056, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13056:ℝ)) (by norm_num [em13056]) ?_)
      (show bm13056^8 ≤ scalar13056.lowerTail by norm_num [bm13056, scalar13056])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13056, bm13056, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13056 :
    agent13056.root+dsL+scalar13056.worldRadius < √(1/100/aL) ∧
    2*(agent13056.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13056, agent13056, scalar13056, tp13056, tm13056, ep13056, em13056, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13056, agent13056, scalar13056, tp13056, tm13056, ep13056, em13056, dsL]

noncomputable def master13056 : MasterCertificate 13056 world13056 agent13056 :=
  master scalar13056 dsL tp13056 tm13056 ep13056 em13056
    (by norm_num [dsL]) (by norm_num [tp13056]) (by norm_num [tm13056])
    (by norm_num [ep13056]) (by norm_num [em13056])
    positive13056 negative13056 tails13056.1 tails13056.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13056.1 tailGuards13056.2

theorem preserves13056 : master13056.toScalarCertificate = scalar13056 := rfl

noncomputable def tp13057 : ℝ := (586848083 / 2500000000)
noncomputable def tm13057 : ℝ := (-((245244647 / 400000000)))
noncomputable def ep13057 : ℝ := (26167731118205113 / 50000000000000000000)
noncomputable def em13057 : ℝ := (25449204459787629 / 50000000000000000000)
noncomputable def bp13057 : ℝ := (1702527987716670739 / 4000000000000000000)
noncomputable def bm13057 : ℝ := (10893324476685368939 / 25000000000000000000)

theorem positive13057 :
    Eplus aL (agent13057.root+dsL) scalar13057.worldRadius world13057.frame
      agent13057.frame tp13057 ≤ -ep13057 := by
  apply positive_check (eT := (57844263646565316149 / 50000000000000000000)) (y := (1523856152789421357 / 4000000000000000000)) (u := (18296187091921331709 / 12500000000000000000))
  · norm_num [world13057, agent13057, scalar13057, tp13057, tm13057, ep13057, em13057, dsL]
  · norm_num [world13057, agent13057, scalar13057, tp13057, tm13057, ep13057, em13057, dsL]
  · norm_num [world13057, agent13057, scalar13057, tp13057, tm13057, ep13057, em13057, dsL]
  · norm_num [world13057, agent13057, scalar13057, tp13057, tm13057, ep13057, em13057, dsL]
  · norm_num [world13057, agent13057, scalar13057, tp13057, tm13057, ep13057, em13057, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13057, agent13057, tp13057, tm13057, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13057, agent13057, scalar13057, tp13057, tm13057, ep13057, em13057, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13057, agent13057, tp13057, tm13057, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13057, agent13057, scalar13057, tp13057, tm13057, ep13057, em13057, dsL]

theorem negative13057 :
    Eminus aL (agent13057.root+dsL) scalar13057.worldRadius world13057.frame
      agent13057.frame tm13057 ≤ -em13057 := by
  apply negative_check (lo := (68342853140593888897 / 100000000000000000000)) (hi := (34171426570296944449 / 50000000000000000000))
    (y := (-((35810809037104265577 / 50000000000000000000)))) (u := (24429876370255756123 / 50000000000000000000))
  · norm_num [world13057, agent13057, scalar13057, tp13057, tm13057, ep13057, em13057, dsL]
  · norm_num [world13057, agent13057, scalar13057, tp13057, tm13057, ep13057, em13057, dsL]
  · norm_num [world13057, agent13057, scalar13057, tp13057, tm13057, ep13057, em13057, dsL]
  · norm_num [world13057, agent13057, scalar13057, tp13057, tm13057, ep13057, em13057, dsL]
  · norm_num [world13057, agent13057, scalar13057, tp13057, tm13057, ep13057, em13057, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13057, agent13057, tp13057, tm13057, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13057, agent13057, tp13057, tm13057, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13057, agent13057, scalar13057, tp13057, tm13057, ep13057, em13057, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13057, agent13057, tp13057, tm13057, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13057, agent13057, scalar13057, tp13057, tm13057, ep13057, em13057, dsL]

theorem tails13057 :
    exp (-((13057:ℝ)*ep13057)) ≤ scalar13057.upperTail ∧
    exp (-((13057:ℝ)*em13057)) ≤ scalar13057.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13057:ℝ)) (by norm_num [ep13057]) ?_)
      (show bp13057^8 ≤ scalar13057.upperTail by norm_num [bp13057, scalar13057])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13057, bp13057, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13057:ℝ)) (by norm_num [em13057]) ?_)
      (show bm13057^8 ≤ scalar13057.lowerTail by norm_num [bm13057, scalar13057])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13057, bm13057, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13057 :
    agent13057.root+dsL+scalar13057.worldRadius < √(1/100/aL) ∧
    2*(agent13057.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13057, agent13057, scalar13057, tp13057, tm13057, ep13057, em13057, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13057, agent13057, scalar13057, tp13057, tm13057, ep13057, em13057, dsL]

noncomputable def master13057 : MasterCertificate 13057 world13057 agent13057 :=
  master scalar13057 dsL tp13057 tm13057 ep13057 em13057
    (by norm_num [dsL]) (by norm_num [tp13057]) (by norm_num [tm13057])
    (by norm_num [ep13057]) (by norm_num [em13057])
    positive13057 negative13057 tails13057.1 tails13057.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13057.1 tailGuards13057.2

theorem preserves13057 : master13057.toScalarCertificate = scalar13057 := rfl

noncomputable def tp13058 : ℝ := (469493223 / 2000000000)
noncomputable def tm13058 : ℝ := (-((1226254579 / 2000000000)))
noncomputable def ep13058 : ℝ := (10467536155941013 / 20000000000000000000)
noncomputable def em13058 : ℝ := (25450145480084663 / 50000000000000000000)
noncomputable def bp13058 : ℝ := (85117748301731371 / 200000000000000000)
noncomputable def bm13058 : ℝ := (2723074205101010393 / 6250000000000000000)

theorem positive13058 :
    Eplus aL (agent13058.root+dsL) scalar13058.worldRadius world13058.frame
      agent13058.frame tp13058 ≤ -ep13058 := by
  apply positive_check (eT := (57844350943104944837 / 50000000000000000000)) (y := (38097069796926512773 / 100000000000000000000)) (u := (146370471526079400057 / 100000000000000000000))
  · norm_num [world13058, agent13058, scalar13058, tp13058, tm13058, ep13058, em13058, dsL]
  · norm_num [world13058, agent13058, scalar13058, tp13058, tm13058, ep13058, em13058, dsL]
  · norm_num [world13058, agent13058, scalar13058, tp13058, tm13058, ep13058, em13058, dsL]
  · norm_num [world13058, agent13058, scalar13058, tp13058, tm13058, ep13058, em13058, dsL]
  · norm_num [world13058, agent13058, scalar13058, tp13058, tm13058, ep13058, em13058, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13058, agent13058, tp13058, tm13058, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13058, agent13058, scalar13058, tp13058, tm13058, ep13058, em13058, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13058, agent13058, tp13058, tm13058, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13058, agent13058, scalar13058, tp13058, tm13058, ep13058, em13058, dsL]

theorem negative13058 :
    Eminus aL (agent13058.root+dsL) scalar13058.worldRadius world13058.frame
      agent13058.frame tm13058 ≤ -em13058 := by
  apply negative_check (lo := (273370945834030049 / 400000000000000000)) (hi := (68342736458507512251 / 100000000000000000000))
    (y := (-((559543352162944107 / 781250000000000000)))) (u := (12214946613114643359 / 25000000000000000000))
  · norm_num [world13058, agent13058, scalar13058, tp13058, tm13058, ep13058, em13058, dsL]
  · norm_num [world13058, agent13058, scalar13058, tp13058, tm13058, ep13058, em13058, dsL]
  · norm_num [world13058, agent13058, scalar13058, tp13058, tm13058, ep13058, em13058, dsL]
  · norm_num [world13058, agent13058, scalar13058, tp13058, tm13058, ep13058, em13058, dsL]
  · norm_num [world13058, agent13058, scalar13058, tp13058, tm13058, ep13058, em13058, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13058, agent13058, tp13058, tm13058, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13058, agent13058, tp13058, tm13058, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13058, agent13058, scalar13058, tp13058, tm13058, ep13058, em13058, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13058, agent13058, tp13058, tm13058, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13058, agent13058, scalar13058, tp13058, tm13058, ep13058, em13058, dsL]

theorem tails13058 :
    exp (-((13058:ℝ)*ep13058)) ≤ scalar13058.upperTail ∧
    exp (-((13058:ℝ)*em13058)) ≤ scalar13058.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13058:ℝ)) (by norm_num [ep13058]) ?_)
      (show bp13058^8 ≤ scalar13058.upperTail by norm_num [bp13058, scalar13058])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13058, bp13058, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13058:ℝ)) (by norm_num [em13058]) ?_)
      (show bm13058^8 ≤ scalar13058.lowerTail by norm_num [bm13058, scalar13058])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13058, bm13058, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13058 :
    agent13058.root+dsL+scalar13058.worldRadius < √(1/100/aL) ∧
    2*(agent13058.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13058, agent13058, scalar13058, tp13058, tm13058, ep13058, em13058, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13058, agent13058, scalar13058, tp13058, tm13058, ep13058, em13058, dsL]

noncomputable def master13058 : MasterCertificate 13058 world13058 agent13058 :=
  master scalar13058 dsL tp13058 tm13058 ep13058 em13058
    (by norm_num [dsL]) (by norm_num [tp13058]) (by norm_num [tm13058])
    (by norm_num [ep13058]) (by norm_num [em13058])
    positive13058 negative13058 tails13058.1 tails13058.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13058.1 tailGuards13058.2

theorem preserves13058 : master13058.toScalarCertificate = scalar13058 := rfl

noncomputable def tp13059 : ℝ := (2347539939 / 10000000000)
noncomputable def tm13059 : ℝ := (-((3065714693 / 5000000000)))
noncomputable def ep13059 : ℝ := (26169949215566101 / 50000000000000000000)
noncomputable def em13059 : ℝ := (2545108607118009 / 5000000000000000000)
noncomputable def bp13059 : ℝ := (2659659339494785061 / 6250000000000000000)
noncomputable def bm13059 : ℝ := (2178253872487555793 / 5000000000000000000)

theorem positive13059 :
    Eplus aL (agent13059.root+dsL) scalar13059.worldRadius world13059.frame
      agent13059.frame tp13059 ≤ -ep13059 := by
  apply positive_check (eT := (57844438403389431497 / 50000000000000000000)) (y := (38097736909332682507 / 100000000000000000000)) (u := (146371447984910955053 / 100000000000000000000))
  · norm_num [world13059, agent13059, scalar13059, tp13059, tm13059, ep13059, em13059, dsL]
  · norm_num [world13059, agent13059, scalar13059, tp13059, tm13059, ep13059, em13059, dsL]
  · norm_num [world13059, agent13059, scalar13059, tp13059, tm13059, ep13059, em13059, dsL]
  · norm_num [world13059, agent13059, scalar13059, tp13059, tm13059, ep13059, em13059, dsL]
  · norm_num [world13059, agent13059, scalar13059, tp13059, tm13059, ep13059, em13059, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13059, agent13059, tp13059, tm13059, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13059, agent13059, scalar13059, tp13059, tm13059, ep13059, em13059, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13059, agent13059, tp13059, tm13059, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13059, agent13059, scalar13059, tp13059, tm13059, ep13059, em13059, dsL]

theorem negative13059 :
    Eminus aL (agent13059.root+dsL) scalar13059.worldRadius world13059.frame
      agent13059.frame tm13059 ≤ -em13059 := by
  apply negative_check (lo := (34171310345599729093 / 50000000000000000000)) (hi := (68342620691199458187 / 100000000000000000000))
    (y := (-((17905369658792570977 / 25000000000000000000)))) (u := (12214955217532080807 / 25000000000000000000))
  · norm_num [world13059, agent13059, scalar13059, tp13059, tm13059, ep13059, em13059, dsL]
  · norm_num [world13059, agent13059, scalar13059, tp13059, tm13059, ep13059, em13059, dsL]
  · norm_num [world13059, agent13059, scalar13059, tp13059, tm13059, ep13059, em13059, dsL]
  · norm_num [world13059, agent13059, scalar13059, tp13059, tm13059, ep13059, em13059, dsL]
  · norm_num [world13059, agent13059, scalar13059, tp13059, tm13059, ep13059, em13059, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13059, agent13059, tp13059, tm13059, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13059, agent13059, tp13059, tm13059, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13059, agent13059, scalar13059, tp13059, tm13059, ep13059, em13059, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13059, agent13059, tp13059, tm13059, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13059, agent13059, scalar13059, tp13059, tm13059, ep13059, em13059, dsL]

theorem tails13059 :
    exp (-((13059:ℝ)*ep13059)) ≤ scalar13059.upperTail ∧
    exp (-((13059:ℝ)*em13059)) ≤ scalar13059.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13059:ℝ)) (by norm_num [ep13059]) ?_)
      (show bp13059^8 ≤ scalar13059.upperTail by norm_num [bp13059, scalar13059])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13059, bp13059, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13059:ℝ)) (by norm_num [em13059]) ?_)
      (show bm13059^8 ≤ scalar13059.lowerTail by norm_num [bm13059, scalar13059])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13059, bm13059, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13059 :
    agent13059.root+dsL+scalar13059.worldRadius < √(1/100/aL) ∧
    2*(agent13059.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13059, agent13059, scalar13059, tp13059, tm13059, ep13059, em13059, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13059, agent13059, scalar13059, tp13059, tm13059, ep13059, em13059, dsL]

noncomputable def master13059 : MasterCertificate 13059 world13059 agent13059 :=
  master scalar13059 dsL tp13059 tm13059 ep13059 em13059
    (by norm_num [dsL]) (by norm_num [tp13059]) (by norm_num [tm13059])
    (by norm_num [ep13059]) (by norm_num [em13059])
    positive13059 negative13059 tails13059.1 tails13059.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13059.1 tailGuards13059.2

theorem preserves13059 : master13059.toScalarCertificate = scalar13059 := rfl

noncomputable def tp13060 : ℝ := (2347685033 / 10000000000)
noncomputable def tm13060 : ℝ := (-((3065900907 / 5000000000)))
noncomputable def ep13060 : ℝ := (52343461366389231 / 100000000000000000000)
noncomputable def em13060 : ℝ := (50905522437352791 / 100000000000000000000)
noncomputable def bp13060 : ℝ := (42549290449026486329 / 100000000000000000000)
noncomputable def bm13060 : ℝ := (43559923078925238029 / 100000000000000000000)

theorem positive13060 :
    Eplus aL (agent13060.root+dsL) scalar13060.worldRadius world13060.frame
      agent13060.frame tp13060 ≤ -ep13060 := by
  apply positive_check (eT := (28922390901694914633 / 25000000000000000000)) (y := (19048845213672495283 / 50000000000000000000)) (u := (73185689974284165257 / 50000000000000000000))
  · norm_num [world13060, agent13060, scalar13060, tp13060, tm13060, ep13060, em13060, dsL]
  · norm_num [world13060, agent13060, scalar13060, tp13060, tm13060, ep13060, em13060, dsL]
  · norm_num [world13060, agent13060, scalar13060, tp13060, tm13060, ep13060, em13060, dsL]
  · norm_num [world13060, agent13060, scalar13060, tp13060, tm13060, ep13060, em13060, dsL]
  · norm_num [world13060, agent13060, scalar13060, tp13060, tm13060, ep13060, em13060, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13060, agent13060, tp13060, tm13060, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13060, agent13060, scalar13060, tp13060, tm13060, ep13060, em13060, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13060, agent13060, tp13060, tm13060, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13060, agent13060, scalar13060, tp13060, tm13060, ep13060, em13060, dsL]

theorem negative13060 :
    Eminus aL (agent13060.root+dsL) scalar13060.worldRadius world13060.frame
      agent13060.frame tm13060 ≤ -em13060 := by
  apply negative_check (lo := (68341588742076651681 / 100000000000000000000)) (hi := (34170794371038325841 / 50000000000000000000))
    (y := (-((4476221555230225781 / 6250000000000000000)))) (u := (48860765706776151243 / 100000000000000000000))
  · norm_num [world13060, agent13060, scalar13060, tp13060, tm13060, ep13060, em13060, dsL]
  · norm_num [world13060, agent13060, scalar13060, tp13060, tm13060, ep13060, em13060, dsL]
  · norm_num [world13060, agent13060, scalar13060, tp13060, tm13060, ep13060, em13060, dsL]
  · norm_num [world13060, agent13060, scalar13060, tp13060, tm13060, ep13060, em13060, dsL]
  · norm_num [world13060, agent13060, scalar13060, tp13060, tm13060, ep13060, em13060, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13060, agent13060, tp13060, tm13060, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13060, agent13060, tp13060, tm13060, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13060, agent13060, scalar13060, tp13060, tm13060, ep13060, em13060, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13060, agent13060, tp13060, tm13060, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13060, agent13060, scalar13060, tp13060, tm13060, ep13060, em13060, dsL]

theorem tails13060 :
    exp (-((13060:ℝ)*ep13060)) ≤ scalar13060.upperTail ∧
    exp (-((13060:ℝ)*em13060)) ≤ scalar13060.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13060:ℝ)) (by norm_num [ep13060]) ?_)
      (show bp13060^8 ≤ scalar13060.upperTail by norm_num [bp13060, scalar13060])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13060, bp13060, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13060:ℝ)) (by norm_num [em13060]) ?_)
      (show bm13060^8 ≤ scalar13060.lowerTail by norm_num [bm13060, scalar13060])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13060, bm13060, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13060 :
    agent13060.root+dsL+scalar13060.worldRadius < √(1/100/aL) ∧
    2*(agent13060.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13060, agent13060, scalar13060, tp13060, tm13060, ep13060, em13060, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13060, agent13060, scalar13060, tp13060, tm13060, ep13060, em13060, dsL]

noncomputable def master13060 : MasterCertificate 13060 world13060 agent13060 :=
  master scalar13060 dsL tp13060 tm13060 ep13060 em13060
    (by norm_num [dsL]) (by norm_num [tp13060]) (by norm_num [tm13060])
    (by norm_num [ep13060]) (by norm_num [em13060])
    positive13060 negative13060 tails13060.1 tails13060.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13060.1 tailGuards13060.2

theorem preserves13060 : master13060.toScalarCertificate = scalar13060 := rfl

noncomputable def tp13061 : ℝ := (469551749 / 2000000000)
noncomputable def tm13061 : ℝ := (-((38324739 / 62500000)))
noncomputable def ep13061 : ℝ := (52345676106269499 / 100000000000000000000)
noncomputable def em13061 : ℝ := (25453700471329317 / 50000000000000000000)
noncomputable def bp13061 : ℝ := (5318121022876743311 / 12500000000000000000)
noncomputable def bm13061 : ℝ := (8711163106963110573 / 20000000000000000000)

theorem positive13061 :
    Eplus aL (agent13061.root+dsL) scalar13061.worldRadius world13061.frame
      agent13061.frame tp13061 ≤ -ep13061 := by
  apply positive_check (eT := (723060861119220313 / 625000000000000000)) (y := (38098356253075693519 / 100000000000000000000)) (u := (146372354530122916843 / 100000000000000000000))
  · norm_num [world13061, agent13061, scalar13061, tp13061, tm13061, ep13061, em13061, dsL]
  · norm_num [world13061, agent13061, scalar13061, tp13061, tm13061, ep13061, em13061, dsL]
  · norm_num [world13061, agent13061, scalar13061, tp13061, tm13061, ep13061, em13061, dsL]
  · norm_num [world13061, agent13061, scalar13061, tp13061, tm13061, ep13061, em13061, dsL]
  · norm_num [world13061, agent13061, scalar13061, tp13061, tm13061, ep13061, em13061, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13061, agent13061, tp13061, tm13061, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13061, agent13061, scalar13061, tp13061, tm13061, ep13061, em13061, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13061, agent13061, tp13061, tm13061, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13061, agent13061, scalar13061, tp13061, tm13061, ep13061, em13061, dsL]

theorem negative13061 :
    Eminus aL (agent13061.root+dsL) scalar13061.worldRadius world13061.frame
      agent13061.frame tm13061 ≤ -em13061 := by
  apply negative_check (lo := (34170736578819632587 / 50000000000000000000)) (hi := (2733658926305570607 / 4000000000000000000))
    (y := (-((71619474816943770577 / 100000000000000000000)))) (u := (48860799941933737507 / 100000000000000000000))
  · norm_num [world13061, agent13061, scalar13061, tp13061, tm13061, ep13061, em13061, dsL]
  · norm_num [world13061, agent13061, scalar13061, tp13061, tm13061, ep13061, em13061, dsL]
  · norm_num [world13061, agent13061, scalar13061, tp13061, tm13061, ep13061, em13061, dsL]
  · norm_num [world13061, agent13061, scalar13061, tp13061, tm13061, ep13061, em13061, dsL]
  · norm_num [world13061, agent13061, scalar13061, tp13061, tm13061, ep13061, em13061, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13061, agent13061, tp13061, tm13061, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13061, agent13061, tp13061, tm13061, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13061, agent13061, scalar13061, tp13061, tm13061, ep13061, em13061, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13061, agent13061, tp13061, tm13061, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13061, agent13061, scalar13061, tp13061, tm13061, ep13061, em13061, dsL]

theorem tails13061 :
    exp (-((13061:ℝ)*ep13061)) ≤ scalar13061.upperTail ∧
    exp (-((13061:ℝ)*em13061)) ≤ scalar13061.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13061:ℝ)) (by norm_num [ep13061]) ?_)
      (show bp13061^8 ≤ scalar13061.upperTail by norm_num [bp13061, scalar13061])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13061, bp13061, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13061:ℝ)) (by norm_num [em13061]) ?_)
      (show bm13061^8 ≤ scalar13061.lowerTail by norm_num [bm13061, scalar13061])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13061, bm13061, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13061 :
    agent13061.root+dsL+scalar13061.worldRadius < √(1/100/aL) ∧
    2*(agent13061.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13061, agent13061, scalar13061, tp13061, tm13061, ep13061, em13061, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13061, agent13061, scalar13061, tp13061, tm13061, ep13061, em13061, dsL]

noncomputable def master13061 : MasterCertificate 13061 world13061 agent13061 :=
  master scalar13061 dsL tp13061 tm13061 ep13061 em13061
    (by norm_num [dsL]) (by norm_num [tp13061]) (by norm_num [tm13061])
    (by norm_num [ep13061]) (by norm_num [em13061])
    positive13061 negative13061 tails13061.1 tails13061.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13061.1 tailGuards13061.2

theorem preserves13061 : master13061.toScalarCertificate = scalar13061 := rfl

noncomputable def tp13062 : ℝ := (2347832381 / 10000000000)
noncomputable def tm13062 : ℝ := (-((6132114423 / 10000000000)))
noncomputable def ep13062 : ℝ := (10469578116244667 / 20000000000000000000)
noncomputable def em13062 : ℝ := (50909279187063813 / 100000000000000000000)
noncomputable def bp13062 : ℝ := (42540646304540342559 / 100000000000000000000)
noncomputable def bm13062 : ℝ := (2177585417951310363 / 5000000000000000000)

theorem positive13062 :
    Eplus aL (agent13062.root+dsL) scalar13062.worldRadius world13062.frame
      agent13062.frame tp13062 ≤ -ep13062 := by
  apply positive_check (eT := (28922477859647317761 / 25000000000000000000)) (y := (38099020971687202391 / 100000000000000000000)) (u := (7318666374881966341 / 5000000000000000000))
  · norm_num [world13062, agent13062, scalar13062, tp13062, tm13062, ep13062, em13062, dsL]
  · norm_num [world13062, agent13062, scalar13062, tp13062, tm13062, ep13062, em13062, dsL]
  · norm_num [world13062, agent13062, scalar13062, tp13062, tm13062, ep13062, em13062, dsL]
  · norm_num [world13062, agent13062, scalar13062, tp13062, tm13062, ep13062, em13062, dsL]
  · norm_num [world13062, agent13062, scalar13062, tp13062, tm13062, ep13062, em13062, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13062, agent13062, tp13062, tm13062, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13062, agent13062, scalar13062, tp13062, tm13062, ep13062, em13062, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13062, agent13062, tp13062, tm13062, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13062, agent13062, scalar13062, tp13062, tm13062, ep13062, em13062, dsL]

theorem negative13062 :
    Eminus aL (agent13062.root+dsL) scalar13062.worldRadius world13062.frame
      agent13062.frame tm13062 ≤ -em13062 := by
  apply negative_check (lo := (68341358547299593601 / 100000000000000000000)) (hi := (34170679273649796801 / 50000000000000000000))
    (y := (-((4476212688296840951 / 6250000000000000000)))) (u := (9772167005210013557 / 20000000000000000000))
  · norm_num [world13062, agent13062, scalar13062, tp13062, tm13062, ep13062, em13062, dsL]
  · norm_num [world13062, agent13062, scalar13062, tp13062, tm13062, ep13062, em13062, dsL]
  · norm_num [world13062, agent13062, scalar13062, tp13062, tm13062, ep13062, em13062, dsL]
  · norm_num [world13062, agent13062, scalar13062, tp13062, tm13062, ep13062, em13062, dsL]
  · norm_num [world13062, agent13062, scalar13062, tp13062, tm13062, ep13062, em13062, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13062, agent13062, tp13062, tm13062, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13062, agent13062, tp13062, tm13062, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13062, agent13062, scalar13062, tp13062, tm13062, ep13062, em13062, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13062, agent13062, tp13062, tm13062, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13062, agent13062, scalar13062, tp13062, tm13062, ep13062, em13062, dsL]

theorem tails13062 :
    exp (-((13062:ℝ)*ep13062)) ≤ scalar13062.upperTail ∧
    exp (-((13062:ℝ)*em13062)) ≤ scalar13062.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13062:ℝ)) (by norm_num [ep13062]) ?_)
      (show bp13062^8 ≤ scalar13062.upperTail by norm_num [bp13062, scalar13062])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13062, bp13062, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13062:ℝ)) (by norm_num [em13062]) ?_)
      (show bm13062^8 ≤ scalar13062.lowerTail by norm_num [bm13062, scalar13062])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13062, bm13062, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13062 :
    agent13062.root+dsL+scalar13062.worldRadius < √(1/100/aL) ∧
    2*(agent13062.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13062, agent13062, scalar13062, tp13062, tm13062, ep13062, em13062, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13062, agent13062, scalar13062, tp13062, tm13062, ep13062, em13062, dsL]

noncomputable def master13062 : MasterCertificate 13062 world13062 agent13062 :=
  master scalar13062 dsL tp13062 tm13062 ep13062 em13062
    (by norm_num [dsL]) (by norm_num [tp13062]) (by norm_num [tm13062])
    (by norm_num [ep13062]) (by norm_num [em13062])
    positive13062 negative13062 tails13062.1 tails13062.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13062.1 tailGuards13062.2

theorem preserves13062 : master13062.toScalarCertificate = scalar13062 := rfl

noncomputable def tp13063 : ℝ := (2347906157 / 10000000000)
noncomputable def tm13063 : ℝ := (-((1533067689 / 2500000000)))
noncomputable def ep13063 : ℝ := (26175052026022283 / 50000000000000000000)
noncomputable def em13063 : ℝ := (50911156513607071 / 100000000000000000000)
noncomputable def bp13063 : ℝ := (8507265065409156759 / 20000000000000000000)
noncomputable def bm13063 : ℝ := (10886900504679823287 / 25000000000000000000)

theorem positive13063 :
    Eplus aL (agent13063.root+dsL) scalar13063.worldRadius world13063.frame
      agent13063.frame tp13063 ≤ -ep13063 := by
  apply positive_check (eT := (57845043068296537607 / 50000000000000000000)) (y := (38099688500119476811 / 100000000000000000000)) (u := (146374304584478802317 / 100000000000000000000))
  · norm_num [world13063, agent13063, scalar13063, tp13063, tm13063, ep13063, em13063, dsL]
  · norm_num [world13063, agent13063, scalar13063, tp13063, tm13063, ep13063, em13063, dsL]
  · norm_num [world13063, agent13063, scalar13063, tp13063, tm13063, ep13063, em13063, dsL]
  · norm_num [world13063, agent13063, scalar13063, tp13063, tm13063, ep13063, em13063, dsL]
  · norm_num [world13063, agent13063, scalar13063, tp13063, tm13063, ep13063, em13063, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13063, agent13063, tp13063, tm13063, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13063, agent13063, scalar13063, tp13063, tm13063, ep13063, em13063, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13063, agent13063, tp13063, tm13063, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13063, agent13063, scalar13063, tp13063, tm13063, ep13063, em13063, dsL]

theorem negative13063 :
    Eminus aL (agent13063.root+dsL) scalar13063.worldRadius world13063.frame
      agent13063.frame tm13063 ≤ -em13063 := by
  apply negative_check (lo := (17085310810924378689 / 25000000000000000000)) (hi := (68341243243697514757 / 100000000000000000000))
    (y := (-((35809666761192361337 / 50000000000000000000)))) (u := (24430434489817167993 / 50000000000000000000))
  · norm_num [world13063, agent13063, scalar13063, tp13063, tm13063, ep13063, em13063, dsL]
  · norm_num [world13063, agent13063, scalar13063, tp13063, tm13063, ep13063, em13063, dsL]
  · norm_num [world13063, agent13063, scalar13063, tp13063, tm13063, ep13063, em13063, dsL]
  · norm_num [world13063, agent13063, scalar13063, tp13063, tm13063, ep13063, em13063, dsL]
  · norm_num [world13063, agent13063, scalar13063, tp13063, tm13063, ep13063, em13063, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13063, agent13063, tp13063, tm13063, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13063, agent13063, tp13063, tm13063, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13063, agent13063, scalar13063, tp13063, tm13063, ep13063, em13063, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13063, agent13063, tp13063, tm13063, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13063, agent13063, scalar13063, tp13063, tm13063, ep13063, em13063, dsL]

theorem tails13063 :
    exp (-((13063:ℝ)*ep13063)) ≤ scalar13063.upperTail ∧
    exp (-((13063:ℝ)*em13063)) ≤ scalar13063.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13063:ℝ)) (by norm_num [ep13063]) ?_)
      (show bp13063^8 ≤ scalar13063.upperTail by norm_num [bp13063, scalar13063])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13063, bp13063, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13063:ℝ)) (by norm_num [em13063]) ?_)
      (show bm13063^8 ≤ scalar13063.lowerTail by norm_num [bm13063, scalar13063])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13063, bm13063, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13063 :
    agent13063.root+dsL+scalar13063.worldRadius < √(1/100/aL) ∧
    2*(agent13063.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13063, agent13063, scalar13063, tp13063, tm13063, ep13063, em13063, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13063, agent13063, scalar13063, tp13063, tm13063, ep13063, em13063, dsL]

noncomputable def master13063 : MasterCertificate 13063 world13063 agent13063 :=
  master scalar13063 dsL tp13063 tm13063 ep13063 em13063
    (by norm_num [dsL]) (by norm_num [tp13063]) (by norm_num [tm13063])
    (by norm_num [ep13063]) (by norm_num [em13063])
    positive13063 negative13063 tails13063.1 tails13063.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13063.1 tailGuards13063.2

theorem preserves13063 : master13063.toScalarCertificate = scalar13063 := rfl

noncomputable def tp13064 : ℝ := (73374367 / 312500000)
noncomputable def tm13064 : ℝ := (-((3066213403 / 5000000000)))
noncomputable def ep13064 : ℝ := (6544039418777289 / 12500000000000000000)
noncomputable def em13064 : ℝ := (50913031811101183 / 100000000000000000000)
noncomputable def bp13064 : ℝ := (21266003031047164351 / 50000000000000000000)
noncomputable def bm13064 : ℝ := (43543497304008073919 / 100000000000000000000)

theorem positive13064 :
    Eplus aL (agent13064.root+dsL) scalar13064.worldRadius world13064.frame
      agent13064.frame tp13064 ≤ -ep13064 := by
  apply positive_check (eT := (115690259510321281223 / 100000000000000000000)) (y := (38100353148108785929 / 100000000000000000000)) (u := (146375277461584188737 / 100000000000000000000))
  · norm_num [world13064, agent13064, scalar13064, tp13064, tm13064, ep13064, em13064, dsL]
  · norm_num [world13064, agent13064, scalar13064, tp13064, tm13064, ep13064, em13064, dsL]
  · norm_num [world13064, agent13064, scalar13064, tp13064, tm13064, ep13064, em13064, dsL]
  · norm_num [world13064, agent13064, scalar13064, tp13064, tm13064, ep13064, em13064, dsL]
  · norm_num [world13064, agent13064, scalar13064, tp13064, tm13064, ep13064, em13064, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13064, agent13064, tp13064, tm13064, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13064, agent13064, scalar13064, tp13064, tm13064, ep13064, em13064, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13064, agent13064, tp13064, tm13064, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13064, agent13064, scalar13064, tp13064, tm13064, ep13064, em13064, dsL]

theorem negative13064 :
    Eminus aL (agent13064.root+dsL) scalar13064.worldRadius world13064.frame
      agent13064.frame tm13064 ≤ -em13064 := by
  apply negative_check (lo := (68341129083843485759 / 100000000000000000000)) (hi := (213566028387010893 / 312500000000000000))
    (y := (-((14323852279867093473 / 20000000000000000000)))) (u := (24430452109797822403 / 50000000000000000000))
  · norm_num [world13064, agent13064, scalar13064, tp13064, tm13064, ep13064, em13064, dsL]
  · norm_num [world13064, agent13064, scalar13064, tp13064, tm13064, ep13064, em13064, dsL]
  · norm_num [world13064, agent13064, scalar13064, tp13064, tm13064, ep13064, em13064, dsL]
  · norm_num [world13064, agent13064, scalar13064, tp13064, tm13064, ep13064, em13064, dsL]
  · norm_num [world13064, agent13064, scalar13064, tp13064, tm13064, ep13064, em13064, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13064, agent13064, tp13064, tm13064, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13064, agent13064, tp13064, tm13064, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13064, agent13064, scalar13064, tp13064, tm13064, ep13064, em13064, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13064, agent13064, tp13064, tm13064, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13064, agent13064, scalar13064, tp13064, tm13064, ep13064, em13064, dsL]

theorem tails13064 :
    exp (-((13064:ℝ)*ep13064)) ≤ scalar13064.upperTail ∧
    exp (-((13064:ℝ)*em13064)) ≤ scalar13064.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13064:ℝ)) (by norm_num [ep13064]) ?_)
      (show bp13064^8 ≤ scalar13064.upperTail by norm_num [bp13064, scalar13064])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13064, bp13064, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13064:ℝ)) (by norm_num [em13064]) ?_)
      (show bm13064^8 ≤ scalar13064.lowerTail by norm_num [bm13064, scalar13064])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13064, bm13064, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13064 :
    agent13064.root+dsL+scalar13064.worldRadius < √(1/100/aL) ∧
    2*(agent13064.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13064, agent13064, scalar13064, tp13064, tm13064, ep13064, em13064, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13064, agent13064, scalar13064, tp13064, tm13064, ep13064, em13064, dsL]

noncomputable def master13064 : MasterCertificate 13064 world13064 agent13064 :=
  master scalar13064 dsL tp13064 tm13064 ep13064 em13064
    (by norm_num [dsL]) (by norm_num [tp13064]) (by norm_num [tm13064])
    (by norm_num [ep13064]) (by norm_num [em13064])
    positive13064 negative13064 tails13064.1 tails13064.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13064.1 tailGuards13064.2

theorem preserves13064 : master13064.toScalarCertificate = scalar13064 := rfl

noncomputable def tp13065 : ℝ := (1174026683 / 5000000000)
noncomputable def tm13065 : ℝ := (-((3066291437 / 5000000000)))
noncomputable def ep13065 : ℝ := (26177263135590527 / 50000000000000000000)
noncomputable def em13065 : ℝ := (50914906788204727 / 100000000000000000000)
noncomputable def bp13065 : ℝ := (42527687262614855737 / 100000000000000000000)
noncomputable def bm13065 : ℝ := (43539392999890805939 / 100000000000000000000)

theorem positive13065 :
    Eplus aL (agent13065.root+dsL) scalar13065.worldRadius world13065.frame
      agent13065.frame tp13065 ≤ -ep13065 := by
  apply positive_check (eT := (115690433168481030271 / 100000000000000000000)) (y := (38101018573058740741 / 100000000000000000000)) (u := (146376251482441669009 / 100000000000000000000))
  · norm_num [world13065, agent13065, scalar13065, tp13065, tm13065, ep13065, em13065, dsL]
  · norm_num [world13065, agent13065, scalar13065, tp13065, tm13065, ep13065, em13065, dsL]
  · norm_num [world13065, agent13065, scalar13065, tp13065, tm13065, ep13065, em13065, dsL]
  · norm_num [world13065, agent13065, scalar13065, tp13065, tm13065, ep13065, em13065, dsL]
  · norm_num [world13065, agent13065, scalar13065, tp13065, tm13065, ep13065, em13065, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13065, agent13065, tp13065, tm13065, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13065, agent13065, scalar13065, tp13065, tm13065, ep13065, em13065, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13065, agent13065, tp13065, tm13065, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13065, agent13065, scalar13065, tp13065, tm13065, ep13065, em13065, dsL]

theorem negative13065 :
    Eminus aL (agent13065.root+dsL) scalar13065.worldRadius world13065.frame
      agent13065.frame tm13065 ≤ -em13065 := by
  apply negative_check (lo := (17085253697677464231 / 25000000000000000000)) (hi := (2733640591628394277 / 4000000000000000000))
    (y := (-((35809595082235051117 / 50000000000000000000)))) (u := (24430469512803689413 / 50000000000000000000))
  · norm_num [world13065, agent13065, scalar13065, tp13065, tm13065, ep13065, em13065, dsL]
  · norm_num [world13065, agent13065, scalar13065, tp13065, tm13065, ep13065, em13065, dsL]
  · norm_num [world13065, agent13065, scalar13065, tp13065, tm13065, ep13065, em13065, dsL]
  · norm_num [world13065, agent13065, scalar13065, tp13065, tm13065, ep13065, em13065, dsL]
  · norm_num [world13065, agent13065, scalar13065, tp13065, tm13065, ep13065, em13065, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13065, agent13065, tp13065, tm13065, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13065, agent13065, tp13065, tm13065, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13065, agent13065, scalar13065, tp13065, tm13065, ep13065, em13065, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13065, agent13065, tp13065, tm13065, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13065, agent13065, scalar13065, tp13065, tm13065, ep13065, em13065, dsL]

theorem tails13065 :
    exp (-((13065:ℝ)*ep13065)) ≤ scalar13065.upperTail ∧
    exp (-((13065:ℝ)*em13065)) ≤ scalar13065.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13065:ℝ)) (by norm_num [ep13065]) ?_)
      (show bp13065^8 ≤ scalar13065.upperTail by norm_num [bp13065, scalar13065])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13065, bp13065, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13065:ℝ)) (by norm_num [em13065]) ?_)
      (show bm13065^8 ≤ scalar13065.lowerTail by norm_num [bm13065, scalar13065])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13065, bm13065, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13065 :
    agent13065.root+dsL+scalar13065.worldRadius < √(1/100/aL) ∧
    2*(agent13065.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13065, agent13065, scalar13065, tp13065, tm13065, ep13065, em13065, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13065, agent13065, scalar13065, tp13065, tm13065, ep13065, em13065, dsL]

noncomputable def master13065 : MasterCertificate 13065 world13065 agent13065 :=
  master scalar13065 dsL tp13065 tm13065 ep13065 em13065
    (by norm_num [dsL]) (by norm_num [tp13065]) (by norm_num [tm13065])
    (by norm_num [ep13065]) (by norm_num [em13065])
    positive13065 negative13065 tails13065.1 tails13065.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13065.1 tailGuards13065.2

theorem preserves13065 : master13065.toScalarCertificate = scalar13065 := rfl

noncomputable def tp13066 : ℝ := (2348126941 / 10000000000)
noncomputable def tm13066 : ℝ := (-((1226547761 / 2000000000)))
noncomputable def ep13066 : ℝ := (409036998685679 / 781250000000000000)
noncomputable def em13066 : ℝ := (50916780472212321 / 100000000000000000000)
noncomputable def bp13066 : ℝ := (1700934784457448243 / 4000000000000000000)
noncomputable def bm13066 : ℝ := (4353528979800917401 / 10000000000000000000)

theorem positive13066 :
    Eplus aL (agent13066.root+dsL) scalar13066.worldRadius world13066.frame
      agent13066.frame tp13066 ≤ -ep13066 := by
  apply positive_check (eT := (115690606522142191081 / 100000000000000000000)) (y := (7620336729433594339 / 20000000000000000000)) (u := (146377224996229632007 / 100000000000000000000))
  · norm_num [world13066, agent13066, scalar13066, tp13066, tm13066, ep13066, em13066, dsL]
  · norm_num [world13066, agent13066, scalar13066, tp13066, tm13066, ep13066, em13066, dsL]
  · norm_num [world13066, agent13066, scalar13066, tp13066, tm13066, ep13066, em13066, dsL]
  · norm_num [world13066, agent13066, scalar13066, tp13066, tm13066, ep13066, em13066, dsL]
  · norm_num [world13066, agent13066, scalar13066, tp13066, tm13066, ep13066, em13066, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13066, agent13066, tp13066, tm13066, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13066, agent13066, scalar13066, tp13066, tm13066, ep13066, em13066, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13066, agent13066, tp13066, tm13066, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13066, agent13066, scalar13066, tp13066, tm13066, ep13066, em13066, dsL]

theorem negative13066 :
    Eminus aL (agent13066.root+dsL) scalar13066.worldRadius world13066.frame
      agent13066.frame tm13066 ≤ -em13066 := by
  apply negative_check (lo := (34170450510961755637 / 50000000000000000000)) (hi := (2733636040876940451 / 4000000000000000000))
    (y := (-((35809559119729561679 / 50000000000000000000)))) (u := (6107621771106971971 / 12500000000000000000))
  · norm_num [world13066, agent13066, scalar13066, tp13066, tm13066, ep13066, em13066, dsL]
  · norm_num [world13066, agent13066, scalar13066, tp13066, tm13066, ep13066, em13066, dsL]
  · norm_num [world13066, agent13066, scalar13066, tp13066, tm13066, ep13066, em13066, dsL]
  · norm_num [world13066, agent13066, scalar13066, tp13066, tm13066, ep13066, em13066, dsL]
  · norm_num [world13066, agent13066, scalar13066, tp13066, tm13066, ep13066, em13066, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13066, agent13066, tp13066, tm13066, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13066, agent13066, tp13066, tm13066, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13066, agent13066, scalar13066, tp13066, tm13066, ep13066, em13066, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13066, agent13066, tp13066, tm13066, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13066, agent13066, scalar13066, tp13066, tm13066, ep13066, em13066, dsL]

theorem tails13066 :
    exp (-((13066:ℝ)*ep13066)) ≤ scalar13066.upperTail ∧
    exp (-((13066:ℝ)*em13066)) ≤ scalar13066.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13066:ℝ)) (by norm_num [ep13066]) ?_)
      (show bp13066^8 ≤ scalar13066.upperTail by norm_num [bp13066, scalar13066])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13066, bp13066, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13066:ℝ)) (by norm_num [em13066]) ?_)
      (show bm13066^8 ≤ scalar13066.lowerTail by norm_num [bm13066, scalar13066])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13066, bm13066, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13066 :
    agent13066.root+dsL+scalar13066.worldRadius < √(1/100/aL) ∧
    2*(agent13066.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13066, agent13066, scalar13066, tp13066, tm13066, ep13066, em13066, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13066, agent13066, scalar13066, tp13066, tm13066, ep13066, em13066, dsL]

noncomputable def master13066 : MasterCertificate 13066 world13066 agent13066 :=
  master scalar13066 dsL tp13066 tm13066 ep13066 em13066
    (by norm_num [dsL]) (by norm_num [tp13066]) (by norm_num [tm13066])
    (by norm_num [ep13066]) (by norm_num [em13066])
    positive13066 negative13066 tails13066.1 tails13066.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13066.1 tailGuards13066.2

theorem preserves13066 : master13066.toScalarCertificate = scalar13066 := rfl

noncomputable def tp13067 : ℝ := (2348200459 / 10000000000)
noncomputable def tm13067 : ℝ := (-((1533223689 / 2500000000)))
noncomputable def ep13067 : ℝ := (26179472194152779 / 50000000000000000000)
noncomputable def em13067 : ℝ := (12729663309638749 / 25000000000000000000)
noncomputable def bp13067 : ℝ := (21259526430522598593 / 50000000000000000000)
noncomputable def bm13067 : ℝ := (1360349607231054611 / 3125000000000000000)

theorem positive13067 :
    Eplus aL (agent13067.root+dsL) scalar13067.worldRadius world13067.frame
      agent13067.frame tp13067 ≤ -ep13067 := by
  apply positive_check (eT := (115690779499548791869 / 100000000000000000000)) (y := (19051174047669332009 / 50000000000000000000)) (u := (146378197600254650889 / 100000000000000000000))
  · norm_num [world13067, agent13067, scalar13067, tp13067, tm13067, ep13067, em13067, dsL]
  · norm_num [world13067, agent13067, scalar13067, tp13067, tm13067, ep13067, em13067, dsL]
  · norm_num [world13067, agent13067, scalar13067, tp13067, tm13067, ep13067, em13067, dsL]
  · norm_num [world13067, agent13067, scalar13067, tp13067, tm13067, ep13067, em13067, dsL]
  · norm_num [world13067, agent13067, scalar13067, tp13067, tm13067, ep13067, em13067, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13067, agent13067, tp13067, tm13067, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13067, agent13067, scalar13067, tp13067, tm13067, ep13067, em13067, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13067, agent13067, tp13067, tm13067, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13067, agent13067, scalar13067, tp13067, tm13067, ep13067, em13067, dsL]

theorem negative13067 :
    Eminus aL (agent13067.root+dsL) scalar13067.worldRadius world13067.frame
      agent13067.frame tm13067 ≤ -em13067 := by
  apply negative_check (lo := (68340787111425818759 / 100000000000000000000)) (hi := (1708519677785645469 / 2500000000000000000))
    (y := (-((71619047379772162231 / 100000000000000000000)))) (u := (48861008791601384759 / 100000000000000000000))
  · norm_num [world13067, agent13067, scalar13067, tp13067, tm13067, ep13067, em13067, dsL]
  · norm_num [world13067, agent13067, scalar13067, tp13067, tm13067, ep13067, em13067, dsL]
  · norm_num [world13067, agent13067, scalar13067, tp13067, tm13067, ep13067, em13067, dsL]
  · norm_num [world13067, agent13067, scalar13067, tp13067, tm13067, ep13067, em13067, dsL]
  · norm_num [world13067, agent13067, scalar13067, tp13067, tm13067, ep13067, em13067, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13067, agent13067, tp13067, tm13067, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13067, agent13067, tp13067, tm13067, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13067, agent13067, scalar13067, tp13067, tm13067, ep13067, em13067, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13067, agent13067, tp13067, tm13067, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13067, agent13067, scalar13067, tp13067, tm13067, ep13067, em13067, dsL]

theorem tails13067 :
    exp (-((13067:ℝ)*ep13067)) ≤ scalar13067.upperTail ∧
    exp (-((13067:ℝ)*em13067)) ≤ scalar13067.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13067:ℝ)) (by norm_num [ep13067]) ?_)
      (show bp13067^8 ≤ scalar13067.upperTail by norm_num [bp13067, scalar13067])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13067, bp13067, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13067:ℝ)) (by norm_num [em13067]) ?_)
      (show bm13067^8 ≤ scalar13067.lowerTail by norm_num [bm13067, scalar13067])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13067, bm13067, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13067 :
    agent13067.root+dsL+scalar13067.worldRadius < √(1/100/aL) ∧
    2*(agent13067.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13067, agent13067, scalar13067, tp13067, tm13067, ep13067, em13067, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13067, agent13067, scalar13067, tp13067, tm13067, ep13067, em13067, dsL]

noncomputable def master13067 : MasterCertificate 13067 world13067 agent13067 :=
  master scalar13067 dsL tp13067 tm13067 ep13067 em13067
    (by norm_num [dsL]) (by norm_num [tp13067]) (by norm_num [tm13067])
    (by norm_num [ep13067]) (by norm_num [em13067])
    positive13067 negative13067 tails13067.1 tails13067.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13067.1 tailGuards13067.2

theorem preserves13067 : master13067.toScalarCertificate = scalar13067 := rfl

noncomputable def tp13068 : ℝ := (1174136961 / 5000000000)
noncomputable def tm13068 : ℝ := (-((6133050473 / 10000000000)))
noncomputable def ep13068 : ℝ := (10472230279819011 / 20000000000000000000)
noncomputable def em13068 : ℝ := (25460262286669549 / 50000000000000000000)
noncomputable def bp13068 : ℝ := (42514737387616772089 / 100000000000000000000)
noncomputable def bm13068 : ℝ := (4352708626541713401 / 10000000000000000000)

theorem positive13068 :
    Eplus aL (agent13068.root+dsL) scalar13068.worldRadius world13068.frame
      agent13068.frame tp13068 ≤ -ep13068 := by
  apply positive_check (eT := (2313819042301830651 / 2000000000000000000)) (y := (38103011797818863869 / 100000000000000000000)) (u := (146379169119206589741 / 100000000000000000000))
  · norm_num [world13068, agent13068, scalar13068, tp13068, tm13068, ep13068, em13068, dsL]
  · norm_num [world13068, agent13068, scalar13068, tp13068, tm13068, ep13068, em13068, dsL]
  · norm_num [world13068, agent13068, scalar13068, tp13068, tm13068, ep13068, em13068, dsL]
  · norm_num [world13068, agent13068, scalar13068, tp13068, tm13068, ep13068, em13068, dsL]
  · norm_num [world13068, agent13068, scalar13068, tp13068, tm13068, ep13068, em13068, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13068, agent13068, tp13068, tm13068, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13068, agent13068, scalar13068, tp13068, tm13068, ep13068, em13068, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13068, agent13068, tp13068, tm13068, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13068, agent13068, scalar13068, tp13068, tm13068, ep13068, em13068, dsL]

theorem negative13068 :
    Eminus aL (agent13068.root+dsL) scalar13068.worldRadius world13068.frame
      agent13068.frame tm13068 ≤ -em13068 := by
  apply negative_check (lo := (34170337068311278849 / 50000000000000000000)) (hi := (68340674136622557699 / 100000000000000000000))
    (y := (-((35809487099278320187 / 50000000000000000000)))) (u := (48861044548694618431 / 100000000000000000000))
  · norm_num [world13068, agent13068, scalar13068, tp13068, tm13068, ep13068, em13068, dsL]
  · norm_num [world13068, agent13068, scalar13068, tp13068, tm13068, ep13068, em13068, dsL]
  · norm_num [world13068, agent13068, scalar13068, tp13068, tm13068, ep13068, em13068, dsL]
  · norm_num [world13068, agent13068, scalar13068, tp13068, tm13068, ep13068, em13068, dsL]
  · norm_num [world13068, agent13068, scalar13068, tp13068, tm13068, ep13068, em13068, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13068, agent13068, tp13068, tm13068, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13068, agent13068, tp13068, tm13068, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13068, agent13068, scalar13068, tp13068, tm13068, ep13068, em13068, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13068, agent13068, tp13068, tm13068, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13068, agent13068, scalar13068, tp13068, tm13068, ep13068, em13068, dsL]

theorem tails13068 :
    exp (-((13068:ℝ)*ep13068)) ≤ scalar13068.upperTail ∧
    exp (-((13068:ℝ)*em13068)) ≤ scalar13068.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13068:ℝ)) (by norm_num [ep13068]) ?_)
      (show bp13068^8 ≤ scalar13068.upperTail by norm_num [bp13068, scalar13068])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13068, bp13068, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13068:ℝ)) (by norm_num [em13068]) ?_)
      (show bm13068^8 ≤ scalar13068.lowerTail by norm_num [bm13068, scalar13068])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13068, bm13068, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13068 :
    agent13068.root+dsL+scalar13068.worldRadius < √(1/100/aL) ∧
    2*(agent13068.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13068, agent13068, scalar13068, tp13068, tm13068, ep13068, em13068, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13068, agent13068, scalar13068, tp13068, tm13068, ep13068, em13068, dsL]

noncomputable def master13068 : MasterCertificate 13068 world13068 agent13068 :=
  master scalar13068 dsL tp13068 tm13068 ep13068 em13068
    (by norm_num [dsL]) (by norm_num [tp13068]) (by norm_num [tm13068])
    (by norm_num [ep13068]) (by norm_num [em13068])
    positive13068 negative13068 tails13068.1 tails13068.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13068.1 tailGuards13068.2

theorem preserves13068 : master13068.toScalarCertificate = scalar13068 := rfl

noncomputable def tp13069 : ℝ := (587086859 / 2500000000)
noncomputable def tm13069 : ℝ := (-((3066603087 / 5000000000)))
noncomputable def ep13069 : ℝ := (204544366190419 / 390625000000000000)
noncomputable def em13069 : ℝ := (25461197643706963 / 50000000000000000000)
noncomputable def bp13069 : ℝ := (42510422579546971383 / 100000000000000000000)
noncomputable def bm13069 : ℝ := (21761492861765342887 / 50000000000000000000)

theorem positive13069 :
    Eplus aL (agent13069.root+dsL) scalar13069.worldRadius world13069.frame
      agent13069.frame tp13069 ≤ -ep13069 := by
  apply positive_check (eT := (23138225025976462309 / 20000000000000000000)) (y := (19051838430164433237 / 50000000000000000000)) (u := (36595035658855024247 / 25000000000000000000))
  · norm_num [world13069, agent13069, scalar13069, tp13069, tm13069, ep13069, em13069, dsL]
  · norm_num [world13069, agent13069, scalar13069, tp13069, tm13069, ep13069, em13069, dsL]
  · norm_num [world13069, agent13069, scalar13069, tp13069, tm13069, ep13069, em13069, dsL]
  · norm_num [world13069, agent13069, scalar13069, tp13069, tm13069, ep13069, em13069, dsL]
  · norm_num [world13069, agent13069, scalar13069, tp13069, tm13069, ep13069, em13069, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13069, agent13069, tp13069, tm13069, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13069, agent13069, scalar13069, tp13069, tm13069, ep13069, em13069, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13069, agent13069, tp13069, tm13069, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13069, agent13069, scalar13069, tp13069, tm13069, ep13069, em13069, dsL]

theorem negative13069 :
    Eminus aL (agent13069.root+dsL) scalar13069.worldRadius world13069.frame
      agent13069.frame tm13069 ≤ -em13069 := by
  apply negative_check (lo := (68340561172841800637 / 100000000000000000000)) (hi := (34170280586420900319 / 50000000000000000000))
    (y := (-((71618902150906881197 / 100000000000000000000)))) (u := (3053817484496346569 / 6250000000000000000))
  · norm_num [world13069, agent13069, scalar13069, tp13069, tm13069, ep13069, em13069, dsL]
  · norm_num [world13069, agent13069, scalar13069, tp13069, tm13069, ep13069, em13069, dsL]
  · norm_num [world13069, agent13069, scalar13069, tp13069, tm13069, ep13069, em13069, dsL]
  · norm_num [world13069, agent13069, scalar13069, tp13069, tm13069, ep13069, em13069, dsL]
  · norm_num [world13069, agent13069, scalar13069, tp13069, tm13069, ep13069, em13069, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13069, agent13069, tp13069, tm13069, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13069, agent13069, tp13069, tm13069, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13069, agent13069, scalar13069, tp13069, tm13069, ep13069, em13069, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13069, agent13069, tp13069, tm13069, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13069, agent13069, scalar13069, tp13069, tm13069, ep13069, em13069, dsL]

theorem tails13069 :
    exp (-((13069:ℝ)*ep13069)) ≤ scalar13069.upperTail ∧
    exp (-((13069:ℝ)*em13069)) ≤ scalar13069.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13069:ℝ)) (by norm_num [ep13069]) ?_)
      (show bp13069^8 ≤ scalar13069.upperTail by norm_num [bp13069, scalar13069])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13069, bp13069, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13069:ℝ)) (by norm_num [em13069]) ?_)
      (show bm13069^8 ≤ scalar13069.lowerTail by norm_num [bm13069, scalar13069])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13069, bm13069, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13069 :
    agent13069.root+dsL+scalar13069.worldRadius < √(1/100/aL) ∧
    2*(agent13069.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13069, agent13069, scalar13069, tp13069, tm13069, ep13069, em13069, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13069, agent13069, scalar13069, tp13069, tm13069, ep13069, em13069, dsL]

noncomputable def master13069 : MasterCertificate 13069 world13069 agent13069 :=
  master scalar13069 dsL tp13069 tm13069 ep13069 em13069
    (by norm_num [dsL]) (by norm_num [tp13069]) (by norm_num [tm13069])
    (by norm_num [ep13069]) (by norm_num [em13069])
    positive13069 negative13069 tails13069.1 tails13069.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13069.1 tailGuards13069.2

theorem preserves13069 : master13069.toScalarCertificate = scalar13069 := rfl

noncomputable def tp13070 : ℝ := (2348492069 / 10000000000)
noncomputable def tm13070 : ℝ := (-((1533394391 / 2500000000)))
noncomputable def ep13070 : ℝ := (5236690697063359 / 10000000000000000000)
noncomputable def em13070 : ℝ := (10185146530009943 / 20000000000000000000)
noncomputable def bp13070 : ℝ := (42505175430655279961 / 100000000000000000000)
noncomputable def bm13070 : ℝ := (21758921302377674223 / 50000000000000000000)

theorem positive13070 :
    Eplus aL (agent13070.root+dsL) scalar13070.worldRadius world13070.frame
      agent13070.frame tp13070 ≤ -ep13070 := by
  apply positive_check (eT := (57845904421009732393 / 50000000000000000000)) (y := (38103627333119062649 / 100000000000000000000)) (u := (146380070137437695921 / 100000000000000000000))
  · norm_num [world13070, agent13070, scalar13070, tp13070, tm13070, ep13070, em13070, dsL]
  · norm_num [world13070, agent13070, scalar13070, tp13070, tm13070, ep13070, em13070, dsL]
  · norm_num [world13070, agent13070, scalar13070, tp13070, tm13070, ep13070, em13070, dsL]
  · norm_num [world13070, agent13070, scalar13070, tp13070, tm13070, ep13070, em13070, dsL]
  · norm_num [world13070, agent13070, scalar13070, tp13070, tm13070, ep13070, em13070, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13070, agent13070, tp13070, tm13070, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13070, agent13070, scalar13070, tp13070, tm13070, ep13070, em13070, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13070, agent13070, tp13070, tm13070, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13070, agent13070, scalar13070, tp13070, tm13070, ep13070, em13070, dsL]

theorem negative13070 :
    Eminus aL (agent13070.root+dsL) scalar13070.worldRadius world13070.frame
      agent13070.frame tm13070 ≤ -em13070 := by
  apply negative_check (lo := (17084883324900748377 / 25000000000000000000)) (hi := (68339533299602993509 / 100000000000000000000))
    (y := (-((35808483629178922959 / 50000000000000000000)))) (u := (24431012585239715267 / 50000000000000000000))
  · norm_num [world13070, agent13070, scalar13070, tp13070, tm13070, ep13070, em13070, dsL]
  · norm_num [world13070, agent13070, scalar13070, tp13070, tm13070, ep13070, em13070, dsL]
  · norm_num [world13070, agent13070, scalar13070, tp13070, tm13070, ep13070, em13070, dsL]
  · norm_num [world13070, agent13070, scalar13070, tp13070, tm13070, ep13070, em13070, dsL]
  · norm_num [world13070, agent13070, scalar13070, tp13070, tm13070, ep13070, em13070, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13070, agent13070, tp13070, tm13070, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13070, agent13070, tp13070, tm13070, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13070, agent13070, scalar13070, tp13070, tm13070, ep13070, em13070, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13070, agent13070, tp13070, tm13070, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13070, agent13070, scalar13070, tp13070, tm13070, ep13070, em13070, dsL]

theorem tails13070 :
    exp (-((13070:ℝ)*ep13070)) ≤ scalar13070.upperTail ∧
    exp (-((13070:ℝ)*em13070)) ≤ scalar13070.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13070:ℝ)) (by norm_num [ep13070]) ?_)
      (show bp13070^8 ≤ scalar13070.upperTail by norm_num [bp13070, scalar13070])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13070, bp13070, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13070:ℝ)) (by norm_num [em13070]) ?_)
      (show bm13070^8 ≤ scalar13070.lowerTail by norm_num [bm13070, scalar13070])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13070, bm13070, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13070 :
    agent13070.root+dsL+scalar13070.worldRadius < √(1/100/aL) ∧
    2*(agent13070.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13070, agent13070, scalar13070, tp13070, tm13070, ep13070, em13070, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13070, agent13070, scalar13070, tp13070, tm13070, ep13070, em13070, dsL]

noncomputable def master13070 : MasterCertificate 13070 world13070 agent13070 :=
  master scalar13070 dsL tp13070 tm13070 ep13070 em13070
    (by norm_num [dsL]) (by norm_num [tp13070]) (by norm_num [tm13070])
    (by norm_num [ep13070]) (by norm_num [em13070])
    positive13070 negative13070 tails13070.1 tails13070.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13070.1 tailGuards13070.2

theorem preserves13070 : master13070.toScalarCertificate = scalar13070 := rfl

noncomputable def tp13071 : ℝ := (1174282729 / 5000000000)
noncomputable def tm13071 : ℝ := (-((3066866603 / 5000000000)))
noncomputable def ep13071 : ℝ := (5236911066557323 / 10000000000000000000)
noncomputable def em13071 : ℝ := (6365950112675387 / 12500000000000000000)
noncomputable def bp13071 : ℝ := (8500172578701919177 / 20000000000000000000)
noncomputable def bm13071 : ℝ := (8702748839559440049 / 20000000000000000000)

theorem positive13071 :
    Eplus aL (agent13071.root+dsL) scalar13071.worldRadius world13071.frame
      agent13071.frame tp13071 ≤ -ep13071 := by
  apply positive_check (eT := (5784599050768062969 / 5000000000000000000)) (y := (19052145389887022007 / 50000000000000000000)) (u := (146381041294338132551 / 100000000000000000000))
  · norm_num [world13071, agent13071, scalar13071, tp13071, tm13071, ep13071, em13071, dsL]
  · norm_num [world13071, agent13071, scalar13071, tp13071, tm13071, ep13071, em13071, dsL]
  · norm_num [world13071, agent13071, scalar13071, tp13071, tm13071, ep13071, em13071, dsL]
  · norm_num [world13071, agent13071, scalar13071, tp13071, tm13071, ep13071, em13071, dsL]
  · norm_num [world13071, agent13071, scalar13071, tp13071, tm13071, ep13071, em13071, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13071, agent13071, tp13071, tm13071, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13071, agent13071, scalar13071, tp13071, tm13071, ep13071, em13071, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13071, agent13071, tp13071, tm13071, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13071, agent13071, scalar13071, tp13071, tm13071, ep13071, em13071, dsL]

theorem negative13071 :
    Eminus aL (agent13071.root+dsL) scalar13071.worldRadius world13071.frame
      agent13071.frame tm13071 ≤ -em13071 := by
  apply negative_check (lo := (68339420493113605487 / 100000000000000000000)) (hi := (4271213780819600343 / 6250000000000000000))
    (y := (-((35808447616006952893 / 50000000000000000000)))) (u := (48862060364022410247 / 100000000000000000000))
  · norm_num [world13071, agent13071, scalar13071, tp13071, tm13071, ep13071, em13071, dsL]
  · norm_num [world13071, agent13071, scalar13071, tp13071, tm13071, ep13071, em13071, dsL]
  · norm_num [world13071, agent13071, scalar13071, tp13071, tm13071, ep13071, em13071, dsL]
  · norm_num [world13071, agent13071, scalar13071, tp13071, tm13071, ep13071, em13071, dsL]
  · norm_num [world13071, agent13071, scalar13071, tp13071, tm13071, ep13071, em13071, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13071, agent13071, tp13071, tm13071, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13071, agent13071, tp13071, tm13071, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13071, agent13071, scalar13071, tp13071, tm13071, ep13071, em13071, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13071, agent13071, tp13071, tm13071, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13071, agent13071, scalar13071, tp13071, tm13071, ep13071, em13071, dsL]

theorem tails13071 :
    exp (-((13071:ℝ)*ep13071)) ≤ scalar13071.upperTail ∧
    exp (-((13071:ℝ)*em13071)) ≤ scalar13071.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13071:ℝ)) (by norm_num [ep13071]) ?_)
      (show bp13071^8 ≤ scalar13071.upperTail by norm_num [bp13071, scalar13071])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13071, bp13071, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13071:ℝ)) (by norm_num [em13071]) ?_)
      (show bm13071^8 ≤ scalar13071.lowerTail by norm_num [bm13071, scalar13071])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13071, bm13071, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13071 :
    agent13071.root+dsL+scalar13071.worldRadius < √(1/100/aL) ∧
    2*(agent13071.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13071, agent13071, scalar13071, tp13071, tm13071, ep13071, em13071, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13071, agent13071, scalar13071, tp13071, tm13071, ep13071, em13071, dsL]

noncomputable def master13071 : MasterCertificate 13071 world13071 agent13071 :=
  master scalar13071 dsL tp13071 tm13071 ep13071 em13071
    (by norm_num [dsL]) (by norm_num [tp13071]) (by norm_num [tm13071])
    (by norm_num [ep13071]) (by norm_num [em13071])
    positive13071 negative13071 tails13071.1 tails13071.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13071.1 tailGuards13071.2

theorem preserves13071 : master13071.toScalarCertificate = scalar13071 := rfl

noncomputable def tp13072 : ℝ := (469727761 / 2000000000)
noncomputable def tm13072 : ℝ := (-((6133888527 / 10000000000)))
noncomputable def ep13072 : ℝ := (52371313370698001 / 100000000000000000000)
noncomputable def em13072 : ℝ := (50929468247358303 / 100000000000000000000)
noncomputable def bp13072 : ℝ := (1062413781177691181 / 2500000000000000000)
noncomputable def bm13072 : ℝ := (5438705827161320671 / 12500000000000000000)

theorem positive13072 :
    Eplus aL (agent13072.root+dsL) scalar13072.worldRadius world13072.frame
      agent13072.frame tp13072 ≤ -ep13072 := by
  apply positive_check (eT := (115692152920188079783 / 100000000000000000000)) (y := (19052476930834698787 / 50000000000000000000)) (u := (36595502980934803921 / 25000000000000000000))
  · norm_num [world13072, agent13072, scalar13072, tp13072, tm13072, ep13072, em13072, dsL]
  · norm_num [world13072, agent13072, scalar13072, tp13072, tm13072, ep13072, em13072, dsL]
  · norm_num [world13072, agent13072, scalar13072, tp13072, tm13072, ep13072, em13072, dsL]
  · norm_num [world13072, agent13072, scalar13072, tp13072, tm13072, ep13072, em13072, dsL]
  · norm_num [world13072, agent13072, scalar13072, tp13072, tm13072, ep13072, em13072, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13072, agent13072, tp13072, tm13072, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13072, agent13072, scalar13072, tp13072, tm13072, ep13072, em13072, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13072, agent13072, tp13072, tm13072, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13072, agent13072, scalar13072, tp13072, tm13072, ep13072, em13072, dsL]

theorem negative13072 :
    Eminus aL (agent13072.root+dsL) scalar13072.worldRadius world13072.frame
      agent13072.frame tm13072 ≤ -em13072 := by
  apply negative_check (lo := (68339308991248911633 / 100000000000000000000)) (hi := (34169654495624455817 / 50000000000000000000))
    (y := (-((2864672839939133049 / 4000000000000000000)))) (u := (48862096636070838491 / 100000000000000000000))
  · norm_num [world13072, agent13072, scalar13072, tp13072, tm13072, ep13072, em13072, dsL]
  · norm_num [world13072, agent13072, scalar13072, tp13072, tm13072, ep13072, em13072, dsL]
  · norm_num [world13072, agent13072, scalar13072, tp13072, tm13072, ep13072, em13072, dsL]
  · norm_num [world13072, agent13072, scalar13072, tp13072, tm13072, ep13072, em13072, dsL]
  · norm_num [world13072, agent13072, scalar13072, tp13072, tm13072, ep13072, em13072, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13072, agent13072, tp13072, tm13072, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13072, agent13072, tp13072, tm13072, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13072, agent13072, scalar13072, tp13072, tm13072, ep13072, em13072, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13072, agent13072, tp13072, tm13072, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13072, agent13072, scalar13072, tp13072, tm13072, ep13072, em13072, dsL]

theorem tails13072 :
    exp (-((13072:ℝ)*ep13072)) ≤ scalar13072.upperTail ∧
    exp (-((13072:ℝ)*em13072)) ≤ scalar13072.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13072:ℝ)) (by norm_num [ep13072]) ?_)
      (show bp13072^8 ≤ scalar13072.upperTail by norm_num [bp13072, scalar13072])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13072, bp13072, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13072:ℝ)) (by norm_num [em13072]) ?_)
      (show bm13072^8 ≤ scalar13072.lowerTail by norm_num [bm13072, scalar13072])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13072, bm13072, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13072 :
    agent13072.root+dsL+scalar13072.worldRadius < √(1/100/aL) ∧
    2*(agent13072.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13072, agent13072, scalar13072, tp13072, tm13072, ep13072, em13072, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13072, agent13072, scalar13072, tp13072, tm13072, ep13072, em13072, dsL]

noncomputable def master13072 : MasterCertificate 13072 world13072 agent13072 :=
  master scalar13072 dsL tp13072 tm13072 ep13072 em13072
    (by norm_num [dsL]) (by norm_num [tp13072]) (by norm_num [tm13072])
    (by norm_num [ep13072]) (by norm_num [em13072])
    positive13072 negative13072 tails13072.1 tails13072.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13072.1 tailGuards13072.2

theorem preserves13072 : master13072.toScalarCertificate = scalar13072 := rfl

noncomputable def tp13073 : ℝ := (587178037 / 2500000000)
noncomputable def tm13073 : ℝ := (-((1533510959 / 2500000000)))
noncomputable def ep13073 : ℝ := (52373515477216481 / 100000000000000000000)
noncomputable def em13073 : ℝ := (50931335040305883 / 100000000000000000000)
noncomputable def bp13073 : ℝ := (8498448043955772311 / 20000000000000000000)
noncomputable def bm13073 : ℝ := (21752774806347787051 / 50000000000000000000)

theorem positive13073 :
    Eplus aL (agent13073.root+dsL) scalar13073.worldRadius world13073.frame
      agent13073.frame tp13073 ≤ -ep13073 := by
  apply positive_check (eT := (115692324829363483047 / 100000000000000000000)) (y := (38105616987871357121 / 100000000000000000000)) (u := (146382982624433719313 / 100000000000000000000))
  · norm_num [world13073, agent13073, scalar13073, tp13073, tm13073, ep13073, em13073, dsL]
  · norm_num [world13073, agent13073, scalar13073, tp13073, tm13073, ep13073, em13073, dsL]
  · norm_num [world13073, agent13073, scalar13073, tp13073, tm13073, ep13073, em13073, dsL]
  · norm_num [world13073, agent13073, scalar13073, tp13073, tm13073, ep13073, em13073, dsL]
  · norm_num [world13073, agent13073, scalar13073, tp13073, tm13073, ep13073, em13073, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13073, agent13073, tp13073, tm13073, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13073, agent13073, scalar13073, tp13073, tm13073, ep13073, em13073, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13073, agent13073, tp13073, tm13073, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13073, agent13073, scalar13073, tp13073, tm13073, ep13073, em13073, dsL]

theorem negative13073 :
    Eminus aL (agent13073.root+dsL) scalar13073.worldRadius world13073.frame
      agent13073.frame tm13073 ≤ -em13073 := by
  apply negative_check (lo := (68339197483373525873 / 100000000000000000000)) (hi := (34169598741686762937 / 50000000000000000000))
    (y := (-((35808373414066466713 / 50000000000000000000)))) (u := (48862132877270119737 / 100000000000000000000))
  · norm_num [world13073, agent13073, scalar13073, tp13073, tm13073, ep13073, em13073, dsL]
  · norm_num [world13073, agent13073, scalar13073, tp13073, tm13073, ep13073, em13073, dsL]
  · norm_num [world13073, agent13073, scalar13073, tp13073, tm13073, ep13073, em13073, dsL]
  · norm_num [world13073, agent13073, scalar13073, tp13073, tm13073, ep13073, em13073, dsL]
  · norm_num [world13073, agent13073, scalar13073, tp13073, tm13073, ep13073, em13073, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13073, agent13073, tp13073, tm13073, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13073, agent13073, tp13073, tm13073, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13073, agent13073, scalar13073, tp13073, tm13073, ep13073, em13073, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13073, agent13073, tp13073, tm13073, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13073, agent13073, scalar13073, tp13073, tm13073, ep13073, em13073, dsL]

theorem tails13073 :
    exp (-((13073:ℝ)*ep13073)) ≤ scalar13073.upperTail ∧
    exp (-((13073:ℝ)*em13073)) ≤ scalar13073.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13073:ℝ)) (by norm_num [ep13073]) ?_)
      (show bp13073^8 ≤ scalar13073.upperTail by norm_num [bp13073, scalar13073])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13073, bp13073, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13073:ℝ)) (by norm_num [em13073]) ?_)
      (show bm13073^8 ≤ scalar13073.lowerTail by norm_num [bm13073, scalar13073])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13073, bm13073, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13073 :
    agent13073.root+dsL+scalar13073.worldRadius < √(1/100/aL) ∧
    2*(agent13073.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13073, agent13073, scalar13073, tp13073, tm13073, ep13073, em13073, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13073, agent13073, scalar13073, tp13073, tm13073, ep13073, em13073, dsL]

noncomputable def master13073 : MasterCertificate 13073 world13073 agent13073 :=
  master scalar13073 dsL tp13073 tm13073 ep13073 em13073
    (by norm_num [dsL]) (by norm_num [tp13073]) (by norm_num [tm13073])
    (by norm_num [ep13073]) (by norm_num [em13073])
    positive13073 negative13073 tails13073.1 tails13073.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13073.1 tailGuards13073.2

theorem preserves13073 : master13073.toScalarCertificate = scalar13073 := rfl

noncomputable def tp13074 : ℝ := (587196373 / 2500000000)
noncomputable def tm13074 : ℝ := (-((6134199337 / 10000000000)))
noncomputable def ep13074 : ℝ := (26187857816343181 / 50000000000000000000)
noncomputable def em13074 : ℝ := (10186640007496839 / 20000000000000000000)
noncomputable def bp13074 : ℝ := (21243965375299721693 / 50000000000000000000)
noncomputable def bm13074 : ℝ := (43501454067519635609 / 100000000000000000000)

theorem positive13074 :
    Eplus aL (agent13074.root+dsL) scalar13074.worldRadius world13074.frame
      agent13074.frame tp13074 ≤ -ep13074 := by
  apply positive_check (eT := (115692496778766649877 / 100000000000000000000)) (y := (1190821268671212371 / 3125000000000000000)) (u := (36595988509798316931 / 25000000000000000000))
  · norm_num [world13074, agent13074, scalar13074, tp13074, tm13074, ep13074, em13074, dsL]
  · norm_num [world13074, agent13074, scalar13074, tp13074, tm13074, ep13074, em13074, dsL]
  · norm_num [world13074, agent13074, scalar13074, tp13074, tm13074, ep13074, em13074, dsL]
  · norm_num [world13074, agent13074, scalar13074, tp13074, tm13074, ep13074, em13074, dsL]
  · norm_num [world13074, agent13074, scalar13074, tp13074, tm13074, ep13074, em13074, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13074, agent13074, tp13074, tm13074, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13074, agent13074, scalar13074, tp13074, tm13074, ep13074, em13074, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13074, agent13074, tp13074, tm13074, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13074, agent13074, scalar13074, tp13074, tm13074, ep13074, em13074, dsL]

theorem negative13074 :
    Eminus aL (agent13074.root+dsL) scalar13074.worldRadius world13074.frame
      agent13074.frame tm13074 ≤ -em13074 := by
  apply negative_check (lo := (68339085104330712607 / 100000000000000000000)) (hi := (2135596409510334769 / 3125000000000000000))
    (y := (-((35808337558092833627 / 50000000000000000000)))) (u := (3053885494829352859 / 6250000000000000000))
  · norm_num [world13074, agent13074, scalar13074, tp13074, tm13074, ep13074, em13074, dsL]
  · norm_num [world13074, agent13074, scalar13074, tp13074, tm13074, ep13074, em13074, dsL]
  · norm_num [world13074, agent13074, scalar13074, tp13074, tm13074, ep13074, em13074, dsL]
  · norm_num [world13074, agent13074, scalar13074, tp13074, tm13074, ep13074, em13074, dsL]
  · norm_num [world13074, agent13074, scalar13074, tp13074, tm13074, ep13074, em13074, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13074, agent13074, tp13074, tm13074, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13074, agent13074, tp13074, tm13074, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13074, agent13074, scalar13074, tp13074, tm13074, ep13074, em13074, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13074, agent13074, tp13074, tm13074, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13074, agent13074, scalar13074, tp13074, tm13074, ep13074, em13074, dsL]

theorem tails13074 :
    exp (-((13074:ℝ)*ep13074)) ≤ scalar13074.upperTail ∧
    exp (-((13074:ℝ)*em13074)) ≤ scalar13074.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13074:ℝ)) (by norm_num [ep13074]) ?_)
      (show bp13074^8 ≤ scalar13074.upperTail by norm_num [bp13074, scalar13074])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13074, bp13074, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13074:ℝ)) (by norm_num [em13074]) ?_)
      (show bm13074^8 ≤ scalar13074.lowerTail by norm_num [bm13074, scalar13074])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13074, bm13074, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13074 :
    agent13074.root+dsL+scalar13074.worldRadius < √(1/100/aL) ∧
    2*(agent13074.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13074, agent13074, scalar13074, tp13074, tm13074, ep13074, em13074, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13074, agent13074, scalar13074, tp13074, tm13074, ep13074, em13074, dsL]

noncomputable def master13074 : MasterCertificate 13074 world13074 agent13074 :=
  master scalar13074 dsL tp13074 tm13074 ep13074 em13074
    (by norm_num [dsL]) (by norm_num [tp13074]) (by norm_num [tm13074])
    (by norm_num [ep13074]) (by norm_num [em13074])
    positive13074 negative13074 tails13074.1 tails13074.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13074.1 tailGuards13074.2

theorem preserves13074 : master13074.toScalarCertificate = scalar13074 := rfl

end BstLean.Part268
