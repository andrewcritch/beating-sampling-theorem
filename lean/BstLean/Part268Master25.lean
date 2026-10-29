import BstLean.Part261Checker
import BstLean.Part268Scalar25
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12975 : ℝ := (1170329121 / 5000000000)
noncomputable def tm12975 : ℝ := (-((6116290803 / 10000000000)))
noncomputable def ep12975 : ℝ := (407336165264973 / 781250000000000000)
noncomputable def em12975 : ℝ := (50728888451926941 / 100000000000000000000)
noncomputable def bp12975 : ℝ := (42928687420786213541 / 100000000000000000000)
noncomputable def bm12975 : ℝ := (21960905412053071479 / 50000000000000000000)

theorem positive12975 :
    Eplus aL (agent12975.root+dsL) scalar12975.worldRadius world12975.frame
      agent12975.frame tp12975 ≤ -ep12975 := by
  apply positive_check (eT := (23133880860694094681 / 20000000000000000000)) (y := (38046343541878281551 / 100000000000000000000)) (u := (73148121047937261477 / 50000000000000000000))
  · norm_num [world12975, agent12975, scalar12975, tp12975, tm12975, ep12975, em12975, dsL]
  · norm_num [world12975, agent12975, scalar12975, tp12975, tm12975, ep12975, em12975, dsL]
  · norm_num [world12975, agent12975, scalar12975, tp12975, tm12975, ep12975, em12975, dsL]
  · norm_num [world12975, agent12975, scalar12975, tp12975, tm12975, ep12975, em12975, dsL]
  · norm_num [world12975, agent12975, scalar12975, tp12975, tm12975, ep12975, em12975, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12975, agent12975, tp12975, tm12975, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12975, agent12975, scalar12975, tp12975, tm12975, ep12975, em12975, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12975, agent12975, tp12975, tm12975, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12975, agent12975, scalar12975, tp12975, tm12975, ep12975, em12975, dsL]

theorem negative12975 :
    Eminus aL (agent12975.root+dsL) scalar12975.worldRadius world12975.frame
      agent12975.frame tm12975 ≤ -em12975 := by
  apply negative_check (lo := (170901548375823237 / 250000000000000000)) (hi := (68360619350329294801 / 100000000000000000000))
    (y := (-((35820568053329143341 / 50000000000000000000)))) (u := (763284643886267423 / 1562500000000000000))
  · norm_num [world12975, agent12975, scalar12975, tp12975, tm12975, ep12975, em12975, dsL]
  · norm_num [world12975, agent12975, scalar12975, tp12975, tm12975, ep12975, em12975, dsL]
  · norm_num [world12975, agent12975, scalar12975, tp12975, tm12975, ep12975, em12975, dsL]
  · norm_num [world12975, agent12975, scalar12975, tp12975, tm12975, ep12975, em12975, dsL]
  · norm_num [world12975, agent12975, scalar12975, tp12975, tm12975, ep12975, em12975, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12975, agent12975, tp12975, tm12975, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12975, agent12975, tp12975, tm12975, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12975, agent12975, scalar12975, tp12975, tm12975, ep12975, em12975, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12975, agent12975, tp12975, tm12975, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12975, agent12975, scalar12975, tp12975, tm12975, ep12975, em12975, dsL]

theorem tails12975 :
    exp (-((12975:ℝ)*ep12975)) ≤ scalar12975.upperTail ∧
    exp (-((12975:ℝ)*em12975)) ≤ scalar12975.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12975:ℝ)) (by norm_num [ep12975]) ?_)
      (show bp12975^8 ≤ scalar12975.upperTail by norm_num [bp12975, scalar12975])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12975, bp12975, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12975:ℝ)) (by norm_num [em12975]) ?_)
      (show bm12975^8 ≤ scalar12975.lowerTail by norm_num [bm12975, scalar12975])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12975, bm12975, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12975 :
    agent12975.root+dsL+scalar12975.worldRadius < √(1/100/aL) ∧
    2*(agent12975.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12975, agent12975, scalar12975, tp12975, tm12975, ep12975, em12975, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12975, agent12975, scalar12975, tp12975, tm12975, ep12975, em12975, dsL]

noncomputable def master12975 : MasterCertificate 12975 world12975 agent12975 :=
  master scalar12975 dsL tp12975 tm12975 ep12975 em12975
    (by norm_num [dsL]) (by norm_num [tp12975]) (by norm_num [tm12975])
    (by norm_num [ep12975]) (by norm_num [em12975])
    positive12975 negative12975 tails12975.1 tails12975.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12975.1 tailGuards12975.2

theorem preserves12975 : master12975.toScalarCertificate = scalar12975 := rfl

noncomputable def tp12976 : ℝ := (1828699 / 7812500)
noncomputable def tm12976 : ℝ := (-((1223290717 / 2000000000)))
noncomputable def ep12976 : ℝ := (52141337622554571 / 100000000000000000000)
noncomputable def em12976 : ℝ := (5073085295828293 / 10000000000000000000)
noncomputable def bp12976 : ℝ := (21462141213672093421 / 50000000000000000000)
noncomputable def bm12976 : ℝ := (43917626355192087587 / 100000000000000000000)

theorem positive12976 :
    Eplus aL (agent12976.root+dsL) scalar12976.worldRadius world12976.frame
      agent12976.frame tp12976 ≤ -ep12976 := by
  apply positive_check (eT := (115669595641481676483 / 100000000000000000000)) (y := (19023518259782474501 / 50000000000000000000)) (u := (9143578493731337091 / 6250000000000000000))
  · norm_num [world12976, agent12976, scalar12976, tp12976, tm12976, ep12976, em12976, dsL]
  · norm_num [world12976, agent12976, scalar12976, tp12976, tm12976, ep12976, em12976, dsL]
  · norm_num [world12976, agent12976, scalar12976, tp12976, tm12976, ep12976, em12976, dsL]
  · norm_num [world12976, agent12976, scalar12976, tp12976, tm12976, ep12976, em12976, dsL]
  · norm_num [world12976, agent12976, scalar12976, tp12976, tm12976, ep12976, em12976, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12976, agent12976, tp12976, tm12976, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12976, agent12976, scalar12976, tp12976, tm12976, ep12976, em12976, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12976, agent12976, tp12976, tm12976, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12976, agent12976, scalar12976, tp12976, tm12976, ep12976, em12976, dsL]

theorem negative12976 :
    Eminus aL (agent12976.root+dsL) scalar12976.worldRadius world12976.frame
      agent12976.frame tm12976 ≤ -em12976 := by
  apply negative_check (lo := (34180240707583805483 / 50000000000000000000)) (hi := (68360481415167610967 / 100000000000000000000))
    (y := (-((35820546536911408947 / 50000000000000000000)))) (u := (195400952921436943 / 400000000000000000))
  · norm_num [world12976, agent12976, scalar12976, tp12976, tm12976, ep12976, em12976, dsL]
  · norm_num [world12976, agent12976, scalar12976, tp12976, tm12976, ep12976, em12976, dsL]
  · norm_num [world12976, agent12976, scalar12976, tp12976, tm12976, ep12976, em12976, dsL]
  · norm_num [world12976, agent12976, scalar12976, tp12976, tm12976, ep12976, em12976, dsL]
  · norm_num [world12976, agent12976, scalar12976, tp12976, tm12976, ep12976, em12976, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12976, agent12976, tp12976, tm12976, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12976, agent12976, tp12976, tm12976, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12976, agent12976, scalar12976, tp12976, tm12976, ep12976, em12976, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12976, agent12976, tp12976, tm12976, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12976, agent12976, scalar12976, tp12976, tm12976, ep12976, em12976, dsL]

theorem tails12976 :
    exp (-((12976:ℝ)*ep12976)) ≤ scalar12976.upperTail ∧
    exp (-((12976:ℝ)*em12976)) ≤ scalar12976.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12976:ℝ)) (by norm_num [ep12976]) ?_)
      (show bp12976^8 ≤ scalar12976.upperTail by norm_num [bp12976, scalar12976])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12976, bp12976, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12976:ℝ)) (by norm_num [em12976]) ?_)
      (show bm12976^8 ≤ scalar12976.lowerTail by norm_num [bm12976, scalar12976])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12976, bm12976, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12976 :
    agent12976.root+dsL+scalar12976.worldRadius < √(1/100/aL) ∧
    2*(agent12976.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12976, agent12976, scalar12976, tp12976, tm12976, ep12976, em12976, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12976, agent12976, scalar12976, tp12976, tm12976, ep12976, em12976, dsL]

noncomputable def master12976 : MasterCertificate 12976 world12976 agent12976 :=
  master scalar12976 dsL tp12976 tm12976 ep12976 em12976
    (by norm_num [dsL]) (by norm_num [tp12976]) (by norm_num [tm12976])
    (by norm_num [ep12976]) (by norm_num [em12976])
    positive12976 negative12976 tails12976.1 tails12976.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12976.1 tailGuards12976.2

theorem preserves12976 : master12976.toScalarCertificate = scalar12976 := rfl

noncomputable def tp12977 : ℝ := (2340811103 / 10000000000)
noncomputable def tm12977 : ℝ := (-((6116616361 / 10000000000)))
noncomputable def ep12977 : ℝ := (52143645010657681 / 100000000000000000000)
noncomputable def em12977 : ℝ := (3170801029422219 / 6250000000000000000)
noncomputable def bp12977 : ℝ := (42919878390492465191 / 100000000000000000000)
noncomputable def bm12977 : ℝ := (8782688555447862043 / 20000000000000000000)

theorem positive12977 :
    Eplus aL (agent12977.root+dsL) scalar12977.worldRadius world12977.frame
      agent12977.frame tp12977 ≤ -ep12977 := by
  apply positive_check (eT := (115669786329108867833 / 100000000000000000000)) (y := (7609545622915928633 / 20000000000000000000)) (u := (73149133843864281949 / 50000000000000000000))
  · norm_num [world12977, agent12977, scalar12977, tp12977, tm12977, ep12977, em12977, dsL]
  · norm_num [world12977, agent12977, scalar12977, tp12977, tm12977, ep12977, em12977, dsL]
  · norm_num [world12977, agent12977, scalar12977, tp12977, tm12977, ep12977, em12977, dsL]
  · norm_num [world12977, agent12977, scalar12977, tp12977, tm12977, ep12977, em12977, dsL]
  · norm_num [world12977, agent12977, scalar12977, tp12977, tm12977, ep12977, em12977, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12977, agent12977, tp12977, tm12977, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12977, agent12977, scalar12977, tp12977, tm12977, ep12977, em12977, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12977, agent12977, tp12977, tm12977, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12977, agent12977, scalar12977, tp12977, tm12977, ep12977, em12977, dsL]

theorem negative12977 :
    Eminus aL (agent12977.root+dsL) scalar12977.worldRadius world12977.frame
      agent12977.frame tm12977 ≤ -em12977 := by
  apply negative_check (lo := (17090085862161909869 / 25000000000000000000)) (hi := (68360343448647639477 / 100000000000000000000))
    (y := (-((35820525233126392959 / 50000000000000000000)))) (u := (24425129522131567343 / 50000000000000000000))
  · norm_num [world12977, agent12977, scalar12977, tp12977, tm12977, ep12977, em12977, dsL]
  · norm_num [world12977, agent12977, scalar12977, tp12977, tm12977, ep12977, em12977, dsL]
  · norm_num [world12977, agent12977, scalar12977, tp12977, tm12977, ep12977, em12977, dsL]
  · norm_num [world12977, agent12977, scalar12977, tp12977, tm12977, ep12977, em12977, dsL]
  · norm_num [world12977, agent12977, scalar12977, tp12977, tm12977, ep12977, em12977, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12977, agent12977, tp12977, tm12977, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12977, agent12977, tp12977, tm12977, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12977, agent12977, scalar12977, tp12977, tm12977, ep12977, em12977, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12977, agent12977, tp12977, tm12977, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12977, agent12977, scalar12977, tp12977, tm12977, ep12977, em12977, dsL]

theorem tails12977 :
    exp (-((12977:ℝ)*ep12977)) ≤ scalar12977.upperTail ∧
    exp (-((12977:ℝ)*em12977)) ≤ scalar12977.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12977:ℝ)) (by norm_num [ep12977]) ?_)
      (show bp12977^8 ≤ scalar12977.upperTail by norm_num [bp12977, scalar12977])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12977, bp12977, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12977:ℝ)) (by norm_num [em12977]) ?_)
      (show bm12977^8 ≤ scalar12977.lowerTail by norm_num [bm12977, scalar12977])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12977, bm12977, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12977 :
    agent12977.root+dsL+scalar12977.worldRadius < √(1/100/aL) ∧
    2*(agent12977.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12977, agent12977, scalar12977, tp12977, tm12977, ep12977, em12977, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12977, agent12977, scalar12977, tp12977, tm12977, ep12977, em12977, dsL]

noncomputable def master12977 : MasterCertificate 12977 world12977 agent12977 :=
  master scalar12977 dsL tp12977 tm12977 ep12977 em12977
    (by norm_num [dsL]) (by norm_num [tp12977]) (by norm_num [tm12977])
    (by norm_num [ep12977]) (by norm_num [em12977])
    positive12977 negative12977 tails12977.1 tails12977.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12977.1 tailGuards12977.2

theorem preserves12977 : master12977.toScalarCertificate = scalar12977 := rfl

noncomputable def tp12978 : ℝ := (1170443757 / 5000000000)
noncomputable def tm12978 : ℝ := (-((764597353 / 1250000000)))
noncomputable def ep12978 : ℝ := (3259121948416903 / 6250000000000000000)
noncomputable def em12978 : ℝ := (10146955767907709 / 20000000000000000000)
noncomputable def bp12978 : ℝ := (2682217213134125371 / 6250000000000000000)
noncomputable def bm12978 : ℝ := (43909260196942383259 / 100000000000000000000)

theorem positive12978 :
    Eplus aL (agent12978.root+dsL) scalar12978.worldRadius world12978.frame
      agent12978.frame tp12978 ≤ -ep12978 := by
  apply positive_check (eT := (28917494312779869727 / 25000000000000000000)) (y := (38048420627286938383 / 100000000000000000000)) (u := (73149640412665451731 / 50000000000000000000))
  · norm_num [world12978, agent12978, scalar12978, tp12978, tm12978, ep12978, em12978, dsL]
  · norm_num [world12978, agent12978, scalar12978, tp12978, tm12978, ep12978, em12978, dsL]
  · norm_num [world12978, agent12978, scalar12978, tp12978, tm12978, ep12978, em12978, dsL]
  · norm_num [world12978, agent12978, scalar12978, tp12978, tm12978, ep12978, em12978, dsL]
  · norm_num [world12978, agent12978, scalar12978, tp12978, tm12978, ep12978, em12978, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12978, agent12978, tp12978, tm12978, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12978, agent12978, scalar12978, tp12978, tm12978, ep12978, em12978, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12978, agent12978, tp12978, tm12978, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12978, agent12978, scalar12978, tp12978, tm12978, ep12978, em12978, dsL]

theorem negative12978 :
    Eminus aL (agent12978.root+dsL) scalar12978.worldRadius world12978.frame
      agent12978.frame tm12978 ≤ -em12978 := by
  apply negative_check (lo := (68360206755878950087 / 100000000000000000000)) (hi := (8545025844484868761 / 12500000000000000000))
    (y := (-((71641005615157760181 / 100000000000000000000)))) (u := (24425140477072076179 / 50000000000000000000))
  · norm_num [world12978, agent12978, scalar12978, tp12978, tm12978, ep12978, em12978, dsL]
  · norm_num [world12978, agent12978, scalar12978, tp12978, tm12978, ep12978, em12978, dsL]
  · norm_num [world12978, agent12978, scalar12978, tp12978, tm12978, ep12978, em12978, dsL]
  · norm_num [world12978, agent12978, scalar12978, tp12978, tm12978, ep12978, em12978, dsL]
  · norm_num [world12978, agent12978, scalar12978, tp12978, tm12978, ep12978, em12978, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12978, agent12978, tp12978, tm12978, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12978, agent12978, tp12978, tm12978, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12978, agent12978, scalar12978, tp12978, tm12978, ep12978, em12978, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12978, agent12978, tp12978, tm12978, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12978, agent12978, scalar12978, tp12978, tm12978, ep12978, em12978, dsL]

theorem tails12978 :
    exp (-((12978:ℝ)*ep12978)) ≤ scalar12978.upperTail ∧
    exp (-((12978:ℝ)*em12978)) ≤ scalar12978.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12978:ℝ)) (by norm_num [ep12978]) ?_)
      (show bp12978^8 ≤ scalar12978.upperTail by norm_num [bp12978, scalar12978])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12978, bp12978, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12978:ℝ)) (by norm_num [em12978]) ?_)
      (show bm12978^8 ≤ scalar12978.lowerTail by norm_num [bm12978, scalar12978])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12978, bm12978, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12978 :
    agent12978.root+dsL+scalar12978.worldRadius < √(1/100/aL) ∧
    2*(agent12978.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12978, agent12978, scalar12978, tp12978, tm12978, ep12978, em12978, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12978, agent12978, scalar12978, tp12978, tm12978, ep12978, em12978, dsL]

noncomputable def master12978 : MasterCertificate 12978 world12978 agent12978 :=
  master scalar12978 dsL tp12978 tm12978 ep12978 em12978
    (by norm_num [dsL]) (by norm_num [tp12978]) (by norm_num [tm12978])
    (by norm_num [ep12978]) (by norm_num [em12978])
    positive12978 negative12978 tails12978.1 tails12978.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12978.1 tailGuards12978.2

theorem preserves12978 : master12978.toScalarCertificate = scalar12978 := rfl

noncomputable def tp12979 : ℝ := (1170481921 / 5000000000)
noncomputable def tm12979 : ℝ := (-((611694141 / 1000000000)))
noncomputable def ep12979 : ℝ := (1303706398920571 / 2500000000000000000)
noncomputable def em12979 : ℝ := (25368369978945593 / 50000000000000000000)
noncomputable def bp12979 : ℝ := (42911073596105447837 / 100000000000000000000)
noncomputable def bm12979 : ℝ := (21952539345156253087 / 50000000000000000000)

theorem positive12979 :
    Eplus aL (agent12979.root+dsL) scalar12979.worldRadius world12979.frame
      agent12979.frame tp12979 ≤ -ep12979 := by
  apply positive_check (eT := (57835083804545677049 / 50000000000000000000)) (y := (38049111965686648673 / 100000000000000000000)) (u := (29260058450386787037 / 20000000000000000000))
  · norm_num [world12979, agent12979, scalar12979, tp12979, tm12979, ep12979, em12979, dsL]
  · norm_num [world12979, agent12979, scalar12979, tp12979, tm12979, ep12979, em12979, dsL]
  · norm_num [world12979, agent12979, scalar12979, tp12979, tm12979, ep12979, em12979, dsL]
  · norm_num [world12979, agent12979, scalar12979, tp12979, tm12979, ep12979, em12979, dsL]
  · norm_num [world12979, agent12979, scalar12979, tp12979, tm12979, ep12979, em12979, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12979, agent12979, tp12979, tm12979, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12979, agent12979, scalar12979, tp12979, tm12979, ep12979, em12979, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12979, agent12979, tp12979, tm12979, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12979, agent12979, scalar12979, tp12979, tm12979, ep12979, em12979, dsL]

theorem negative12979 :
    Eminus aL (agent12979.root+dsL) scalar12979.worldRadius world12979.frame
      agent12979.frame tm12979 ≤ -em12979 := by
  apply negative_check (lo := (68360069483341979781 / 100000000000000000000)) (hi := (34180034741670989891 / 50000000000000000000))
    (y := (-((71640962427272923697 / 100000000000000000000)))) (u := (24425151025775894447 / 50000000000000000000))
  · norm_num [world12979, agent12979, scalar12979, tp12979, tm12979, ep12979, em12979, dsL]
  · norm_num [world12979, agent12979, scalar12979, tp12979, tm12979, ep12979, em12979, dsL]
  · norm_num [world12979, agent12979, scalar12979, tp12979, tm12979, ep12979, em12979, dsL]
  · norm_num [world12979, agent12979, scalar12979, tp12979, tm12979, ep12979, em12979, dsL]
  · norm_num [world12979, agent12979, scalar12979, tp12979, tm12979, ep12979, em12979, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12979, agent12979, tp12979, tm12979, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12979, agent12979, tp12979, tm12979, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12979, agent12979, scalar12979, tp12979, tm12979, ep12979, em12979, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12979, agent12979, tp12979, tm12979, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12979, agent12979, scalar12979, tp12979, tm12979, ep12979, em12979, dsL]

theorem tails12979 :
    exp (-((12979:ℝ)*ep12979)) ≤ scalar12979.upperTail ∧
    exp (-((12979:ℝ)*em12979)) ≤ scalar12979.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12979:ℝ)) (by norm_num [ep12979]) ?_)
      (show bp12979^8 ≤ scalar12979.upperTail by norm_num [bp12979, scalar12979])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12979, bp12979, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12979:ℝ)) (by norm_num [em12979]) ?_)
      (show bm12979^8 ≤ scalar12979.lowerTail by norm_num [bm12979, scalar12979])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12979, bm12979, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12979 :
    agent12979.root+dsL+scalar12979.worldRadius < √(1/100/aL) ∧
    2*(agent12979.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12979, agent12979, scalar12979, tp12979, tm12979, ep12979, em12979, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12979, agent12979, scalar12979, tp12979, tm12979, ep12979, em12979, dsL]

noncomputable def master12979 : MasterCertificate 12979 world12979 agent12979 :=
  master scalar12979 dsL tp12979 tm12979 ep12979 em12979
    (by norm_num [dsL]) (by norm_num [tp12979]) (by norm_num [tm12979])
    (by norm_num [ep12979]) (by norm_num [em12979])
    positive12979 negative12979 tails12979.1 tails12979.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12979.1 tailGuards12979.2

theorem preserves12979 : master12979.toScalarCertificate = scalar12979 := rfl

noncomputable def tp12980 : ℝ := (468222431 / 2000000000)
noncomputable def tm12980 : ℝ := (-((611732187 / 1000000000)))
noncomputable def ep12980 : ℝ := (26075961630079101 / 50000000000000000000)
noncomputable def em12980 : ℝ := (5074018810528853 / 10000000000000000000)
noncomputable def bp12980 : ℝ := (2681607716440108879 / 6250000000000000000)
noncomputable def bm12980 : ℝ := (5487479772556173151 / 12500000000000000000)

theorem positive12980 :
    Eplus aL (agent12980.root+dsL) scalar12980.worldRadius world12980.frame
      agent12980.frame tp12980 ≤ -ep12980 := by
  apply positive_check (eT := (115670875774517627577 / 100000000000000000000)) (y := (9512271844537781329 / 25000000000000000000)) (u := (29260051256060405847 / 20000000000000000000))
  · norm_num [world12980, agent12980, scalar12980, tp12980, tm12980, ep12980, em12980, dsL]
  · norm_num [world12980, agent12980, scalar12980, tp12980, tm12980, ep12980, em12980, dsL]
  · norm_num [world12980, agent12980, scalar12980, tp12980, tm12980, ep12980, em12980, dsL]
  · norm_num [world12980, agent12980, scalar12980, tp12980, tm12980, ep12980, em12980, dsL]
  · norm_num [world12980, agent12980, scalar12980, tp12980, tm12980, ep12980, em12980, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12980, agent12980, tp12980, tm12980, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12980, agent12980, scalar12980, tp12980, tm12980, ep12980, em12980, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12980, agent12980, tp12980, tm12980, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12980, agent12980, scalar12980, tp12980, tm12980, ep12980, em12980, dsL]

theorem negative12980 :
    Eminus aL (agent12980.root+dsL) scalar12980.worldRadius world12980.frame
      agent12980.frame tm12980 ≤ -em12980 := by
  apply negative_check (lo := (34179503003754380501 / 50000000000000000000)) (hi := (68359006007508761003 / 100000000000000000000))
    (y := (-((71639045224862832679 / 100000000000000000000)))) (u := (9770247723939596567 / 20000000000000000000))
  · norm_num [world12980, agent12980, scalar12980, tp12980, tm12980, ep12980, em12980, dsL]
  · norm_num [world12980, agent12980, scalar12980, tp12980, tm12980, ep12980, em12980, dsL]
  · norm_num [world12980, agent12980, scalar12980, tp12980, tm12980, ep12980, em12980, dsL]
  · norm_num [world12980, agent12980, scalar12980, tp12980, tm12980, ep12980, em12980, dsL]
  · norm_num [world12980, agent12980, scalar12980, tp12980, tm12980, ep12980, em12980, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12980, agent12980, tp12980, tm12980, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12980, agent12980, tp12980, tm12980, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12980, agent12980, scalar12980, tp12980, tm12980, ep12980, em12980, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12980, agent12980, tp12980, tm12980, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12980, agent12980, scalar12980, tp12980, tm12980, ep12980, em12980, dsL]

theorem tails12980 :
    exp (-((12980:ℝ)*ep12980)) ≤ scalar12980.upperTail ∧
    exp (-((12980:ℝ)*em12980)) ≤ scalar12980.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12980:ℝ)) (by norm_num [ep12980]) ?_)
      (show bp12980^8 ≤ scalar12980.upperTail by norm_num [bp12980, scalar12980])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12980, bp12980, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12980:ℝ)) (by norm_num [em12980]) ?_)
      (show bm12980^8 ≤ scalar12980.lowerTail by norm_num [bm12980, scalar12980])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12980, bm12980, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12980 :
    agent12980.root+dsL+scalar12980.worldRadius < √(1/100/aL) ∧
    2*(agent12980.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12980, agent12980, scalar12980, tp12980, tm12980, ep12980, em12980, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12980, agent12980, scalar12980, tp12980, tm12980, ep12980, em12980, dsL]

noncomputable def master12980 : MasterCertificate 12980 world12980 agent12980 :=
  master scalar12980 dsL tp12980 tm12980 ep12980 em12980
    (by norm_num [dsL]) (by norm_num [tp12980]) (by norm_num [tm12980])
    (by norm_num [ep12980]) (by norm_num [em12980])
    positive12980 negative12980 tails12980.1 tails12980.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12980.1 tailGuards12980.2

theorem preserves12980 : master12980.toScalarCertificate = scalar12980 := rfl

noncomputable def tp12981 : ℝ := (2341188439 / 10000000000)
noncomputable def tm12981 : ℝ := (-((6117484119 / 10000000000)))
noncomputable def ep12981 : ℝ := (26077112820892381 / 50000000000000000000)
noncomputable def em12981 : ℝ := (50742146977986629 / 100000000000000000000)
noncomputable def bp12981 : ℝ := (42901323752866231839 / 100000000000000000000)
noncomputable def bm12981 : ℝ := (43895658658562769527 / 100000000000000000000)

theorem positive12981 :
    Eplus aL (agent12981.root+dsL) scalar12981.worldRadius world12981.frame
      agent12981.frame tp12981 ≤ -ep12981 := by
  apply positive_check (eT := (115671065871770334909 / 100000000000000000000)) (y := (38049778632114985477 / 100000000000000000000)) (u := (29260253518023611993 / 20000000000000000000))
  · norm_num [world12981, agent12981, scalar12981, tp12981, tm12981, ep12981, em12981, dsL]
  · norm_num [world12981, agent12981, scalar12981, tp12981, tm12981, ep12981, em12981, dsL]
  · norm_num [world12981, agent12981, scalar12981, tp12981, tm12981, ep12981, em12981, dsL]
  · norm_num [world12981, agent12981, scalar12981, tp12981, tm12981, ep12981, em12981, dsL]
  · norm_num [world12981, agent12981, scalar12981, tp12981, tm12981, ep12981, em12981, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12981, agent12981, tp12981, tm12981, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12981, agent12981, scalar12981, tp12981, tm12981, ep12981, em12981, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12981, agent12981, tp12981, tm12981, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12981, agent12981, scalar12981, tp12981, tm12981, ep12981, em12981, dsL]

theorem negative12981 :
    Eminus aL (agent12981.root+dsL) scalar12981.worldRadius world12981.frame
      agent12981.frame tm12981 ≤ -em12981 := by
  apply negative_check (lo := (34179435037699222803 / 50000000000000000000)) (hi := (68358870075398445607 / 100000000000000000000))
    (y := (-((14327799965965261841 / 20000000000000000000)))) (u := (48851260795740629827 / 100000000000000000000))
  · norm_num [world12981, agent12981, scalar12981, tp12981, tm12981, ep12981, em12981, dsL]
  · norm_num [world12981, agent12981, scalar12981, tp12981, tm12981, ep12981, em12981, dsL]
  · norm_num [world12981, agent12981, scalar12981, tp12981, tm12981, ep12981, em12981, dsL]
  · norm_num [world12981, agent12981, scalar12981, tp12981, tm12981, ep12981, em12981, dsL]
  · norm_num [world12981, agent12981, scalar12981, tp12981, tm12981, ep12981, em12981, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12981, agent12981, tp12981, tm12981, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12981, agent12981, tp12981, tm12981, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12981, agent12981, scalar12981, tp12981, tm12981, ep12981, em12981, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12981, agent12981, tp12981, tm12981, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12981, agent12981, scalar12981, tp12981, tm12981, ep12981, em12981, dsL]

theorem tails12981 :
    exp (-((12981:ℝ)*ep12981)) ≤ scalar12981.upperTail ∧
    exp (-((12981:ℝ)*em12981)) ≤ scalar12981.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12981:ℝ)) (by norm_num [ep12981]) ?_)
      (show bp12981^8 ≤ scalar12981.upperTail by norm_num [bp12981, scalar12981])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12981, bp12981, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12981:ℝ)) (by norm_num [em12981]) ?_)
      (show bm12981^8 ≤ scalar12981.lowerTail by norm_num [bm12981, scalar12981])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12981, bm12981, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12981 :
    agent12981.root+dsL+scalar12981.worldRadius < √(1/100/aL) ∧
    2*(agent12981.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12981, agent12981, scalar12981, tp12981, tm12981, ep12981, em12981, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12981, agent12981, scalar12981, tp12981, tm12981, ep12981, em12981, dsL]

noncomputable def master12981 : MasterCertificate 12981 world12981 agent12981 :=
  master scalar12981 dsL tp12981 tm12981 ep12981 em12981
    (by norm_num [dsL]) (by norm_num [tp12981]) (by norm_num [tm12981])
    (by norm_num [ep12981]) (by norm_num [em12981])
    positive12981 negative12981 tails12981.1 tails12981.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12981.1 tailGuards12981.2

theorem preserves12981 : master12981.toScalarCertificate = scalar12981 := rfl

noncomputable def tp12982 : ℝ := (2341264753 / 10000000000)
noncomputable def tm12982 : ℝ := (-((122352929 / 200000000)))
noncomputable def ep12982 : ℝ := (26078263402018649 / 50000000000000000000)
noncomputable def em12982 : ℝ := (50744104711125411 / 100000000000000000000)
noncomputable def bp12982 : ℝ := (21448462547879334487 / 50000000000000000000)
noncomputable def bm12982 : ℝ := (43891480131296550759 / 100000000000000000000)

theorem positive12982 :
    Eplus aL (agent12982.root+dsL) scalar12982.worldRadius world12982.frame
      agent12982.frame tp12982 ≤ -ep12982 := by
  apply positive_check (eT := (5783562810888743499 / 5000000000000000000)) (y := (1902523541909094169 / 5000000000000000000)) (u := (146302280299873282437 / 100000000000000000000))
  · norm_num [world12982, agent12982, scalar12982, tp12982, tm12982, ep12982, em12982, dsL]
  · norm_num [world12982, agent12982, scalar12982, tp12982, tm12982, ep12982, em12982, dsL]
  · norm_num [world12982, agent12982, scalar12982, tp12982, tm12982, ep12982, em12982, dsL]
  · norm_num [world12982, agent12982, scalar12982, tp12982, tm12982, ep12982, em12982, dsL]
  · norm_num [world12982, agent12982, scalar12982, tp12982, tm12982, ep12982, em12982, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12982, agent12982, tp12982, tm12982, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12982, agent12982, scalar12982, tp12982, tm12982, ep12982, em12982, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12982, agent12982, tp12982, tm12982, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12982, agent12982, scalar12982, tp12982, tm12982, ep12982, em12982, dsL]

theorem negative12982 :
    Eminus aL (agent12982.root+dsL) scalar12982.worldRadius world12982.frame
      agent12982.frame tm12982 ≤ -em12982 := by
  apply negative_check (lo := (8544841717232203889 / 12500000000000000000)) (hi := (68358733737857631113 / 100000000000000000000))
    (y := (-((71638955992411890049 / 100000000000000000000)))) (u := (48851282210874967759 / 100000000000000000000))
  · norm_num [world12982, agent12982, scalar12982, tp12982, tm12982, ep12982, em12982, dsL]
  · norm_num [world12982, agent12982, scalar12982, tp12982, tm12982, ep12982, em12982, dsL]
  · norm_num [world12982, agent12982, scalar12982, tp12982, tm12982, ep12982, em12982, dsL]
  · norm_num [world12982, agent12982, scalar12982, tp12982, tm12982, ep12982, em12982, dsL]
  · norm_num [world12982, agent12982, scalar12982, tp12982, tm12982, ep12982, em12982, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12982, agent12982, tp12982, tm12982, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12982, agent12982, tp12982, tm12982, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12982, agent12982, scalar12982, tp12982, tm12982, ep12982, em12982, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12982, agent12982, tp12982, tm12982, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12982, agent12982, scalar12982, tp12982, tm12982, ep12982, em12982, dsL]

theorem tails12982 :
    exp (-((12982:ℝ)*ep12982)) ≤ scalar12982.upperTail ∧
    exp (-((12982:ℝ)*em12982)) ≤ scalar12982.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12982:ℝ)) (by norm_num [ep12982]) ?_)
      (show bp12982^8 ≤ scalar12982.upperTail by norm_num [bp12982, scalar12982])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12982, bp12982, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12982:ℝ)) (by norm_num [em12982]) ?_)
      (show bm12982^8 ≤ scalar12982.lowerTail by norm_num [bm12982, scalar12982])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12982, bm12982, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12982 :
    agent12982.root+dsL+scalar12982.worldRadius < √(1/100/aL) ∧
    2*(agent12982.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12982, agent12982, scalar12982, tp12982, tm12982, ep12982, em12982, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12982, agent12982, scalar12982, tp12982, tm12982, ep12982, em12982, dsL]

noncomputable def master12982 : MasterCertificate 12982 world12982 agent12982 :=
  master scalar12982 dsL tp12982 tm12982 ep12982 em12982
    (by norm_num [dsL]) (by norm_num [tp12982]) (by norm_num [tm12982])
    (by norm_num [ep12982]) (by norm_num [em12982])
    positive12982 negative12982 tails12982.1 tails12982.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12982.1 tailGuards12982.2

theorem preserves12982 : master12982.toScalarCertificate = scalar12982 := rfl

noncomputable def tp12983 : ℝ := (1170670437 / 5000000000)
noncomputable def tm12983 : ℝ := (-((6117808421 / 10000000000)))
noncomputable def ep12983 : ℝ := (26079413442960707 / 50000000000000000000)
noncomputable def em12983 : ℝ := (10149212290142763 / 20000000000000000000)
noncomputable def bp12983 : ℝ := (21446263697461539661 / 50000000000000000000)
noncomputable def bm12983 : ℝ := (68573910147870553 / 156250000000000000)

theorem positive12983 :
    Eplus aL (agent12983.root+dsL) scalar12983.worldRadius world12983.frame
      agent12983.frame tp12983 ≤ -ep12983 := by
  apply positive_check (eT := (3614732662768473867 / 3125000000000000000)) (y := (19025579974782739621 / 50000000000000000000)) (u := (4571977765281720571 / 3125000000000000000))
  · norm_num [world12983, agent12983, scalar12983, tp12983, tm12983, ep12983, em12983, dsL]
  · norm_num [world12983, agent12983, scalar12983, tp12983, tm12983, ep12983, em12983, dsL]
  · norm_num [world12983, agent12983, scalar12983, tp12983, tm12983, ep12983, em12983, dsL]
  · norm_num [world12983, agent12983, scalar12983, tp12983, tm12983, ep12983, em12983, dsL]
  · norm_num [world12983, agent12983, scalar12983, tp12983, tm12983, ep12983, em12983, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12983, agent12983, tp12983, tm12983, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12983, agent12983, scalar12983, tp12983, tm12983, ep12983, em12983, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12983, agent12983, tp12983, tm12983, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12983, agent12983, scalar12983, tp12983, tm12983, ep12983, em12983, dsL]

theorem negative12983 :
    Eminus aL (agent12983.root+dsL) scalar12983.worldRadius world12983.frame
      agent12983.frame tm12983 ≤ -em12983 := by
  apply negative_check (lo := (68358598873671205779 / 100000000000000000000)) (hi := (3417929943683560289 / 5000000000000000000))
    (y := (-((35819454586001390489 / 50000000000000000000)))) (u := (48851305083250508387 / 100000000000000000000))
  · norm_num [world12983, agent12983, scalar12983, tp12983, tm12983, ep12983, em12983, dsL]
  · norm_num [world12983, agent12983, scalar12983, tp12983, tm12983, ep12983, em12983, dsL]
  · norm_num [world12983, agent12983, scalar12983, tp12983, tm12983, ep12983, em12983, dsL]
  · norm_num [world12983, agent12983, scalar12983, tp12983, tm12983, ep12983, em12983, dsL]
  · norm_num [world12983, agent12983, scalar12983, tp12983, tm12983, ep12983, em12983, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12983, agent12983, tp12983, tm12983, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12983, agent12983, tp12983, tm12983, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12983, agent12983, scalar12983, tp12983, tm12983, ep12983, em12983, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12983, agent12983, tp12983, tm12983, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12983, agent12983, scalar12983, tp12983, tm12983, ep12983, em12983, dsL]

theorem tails12983 :
    exp (-((12983:ℝ)*ep12983)) ≤ scalar12983.upperTail ∧
    exp (-((12983:ℝ)*em12983)) ≤ scalar12983.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12983:ℝ)) (by norm_num [ep12983]) ?_)
      (show bp12983^8 ≤ scalar12983.upperTail by norm_num [bp12983, scalar12983])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12983, bp12983, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12983:ℝ)) (by norm_num [em12983]) ?_)
      (show bm12983^8 ≤ scalar12983.lowerTail by norm_num [bm12983, scalar12983])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12983, bm12983, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12983 :
    agent12983.root+dsL+scalar12983.worldRadius < √(1/100/aL) ∧
    2*(agent12983.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12983, agent12983, scalar12983, tp12983, tm12983, ep12983, em12983, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12983, agent12983, scalar12983, tp12983, tm12983, ep12983, em12983, dsL]

noncomputable def master12983 : MasterCertificate 12983 world12983 agent12983 :=
  master scalar12983 dsL tp12983 tm12983 ep12983 em12983
    (by norm_num [dsL]) (by norm_num [tp12983]) (by norm_num [tm12983])
    (by norm_num [ep12983]) (by norm_num [em12983])
    positive12983 negative12983 tails12983.1 tails12983.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12983.1 tailGuards12983.2

theorem preserves12983 : master12983.toScalarCertificate = scalar12983 := rfl

noncomputable def tp12984 : ℝ := (2341417103 / 10000000000)
noncomputable def tm12984 : ℝ := (-((3058985287 / 5000000000)))
noncomputable def ep12984 : ℝ := (26080563110277247 / 50000000000000000000)
noncomputable def em12984 : ℝ := (25374008744264063 / 50000000000000000000)
noncomputable def bp12984 : ℝ := (10722032604614277277 / 25000000000000000000)
noncomputable def bm12984 : ℝ := (43883125540759668607 / 100000000000000000000)

theorem positive12984 :
    Eplus aL (agent12984.root+dsL) scalar12984.worldRadius world12984.frame
      agent12984.frame tp12984 ≤ -ep12984 := by
  apply positive_check (eT := (115671635009204568783 / 100000000000000000000)) (y := (19025925662837270581 / 50000000000000000000)) (u := (73152149999247553337 / 50000000000000000000))
  · norm_num [world12984, agent12984, scalar12984, tp12984, tm12984, ep12984, em12984, dsL]
  · norm_num [world12984, agent12984, scalar12984, tp12984, tm12984, ep12984, em12984, dsL]
  · norm_num [world12984, agent12984, scalar12984, tp12984, tm12984, ep12984, em12984, dsL]
  · norm_num [world12984, agent12984, scalar12984, tp12984, tm12984, ep12984, em12984, dsL]
  · norm_num [world12984, agent12984, scalar12984, tp12984, tm12984, ep12984, em12984, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12984, agent12984, tp12984, tm12984, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12984, agent12984, scalar12984, tp12984, tm12984, ep12984, em12984, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12984, agent12984, tp12984, tm12984, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12984, agent12984, scalar12984, tp12984, tm12984, ep12984, em12984, dsL]

theorem negative12984 :
    Eminus aL (agent12984.root+dsL) scalar12984.worldRadius world12984.frame
      agent12984.frame tm12984 ≤ -em12984 := by
  apply negative_check (lo := (34179231589480670689 / 50000000000000000000)) (hi := (68358463178961341379 / 100000000000000000000))
    (y := (-((71638864998807896947 / 100000000000000000000)))) (u := (6106415832804684039 / 12500000000000000000))
  · norm_num [world12984, agent12984, scalar12984, tp12984, tm12984, ep12984, em12984, dsL]
  · norm_num [world12984, agent12984, scalar12984, tp12984, tm12984, ep12984, em12984, dsL]
  · norm_num [world12984, agent12984, scalar12984, tp12984, tm12984, ep12984, em12984, dsL]
  · norm_num [world12984, agent12984, scalar12984, tp12984, tm12984, ep12984, em12984, dsL]
  · norm_num [world12984, agent12984, scalar12984, tp12984, tm12984, ep12984, em12984, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12984, agent12984, tp12984, tm12984, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12984, agent12984, tp12984, tm12984, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12984, agent12984, scalar12984, tp12984, tm12984, ep12984, em12984, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12984, agent12984, tp12984, tm12984, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12984, agent12984, scalar12984, tp12984, tm12984, ep12984, em12984, dsL]

theorem tails12984 :
    exp (-((12984:ℝ)*ep12984)) ≤ scalar12984.upperTail ∧
    exp (-((12984:ℝ)*em12984)) ≤ scalar12984.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12984:ℝ)) (by norm_num [ep12984]) ?_)
      (show bp12984^8 ≤ scalar12984.upperTail by norm_num [bp12984, scalar12984])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12984, bp12984, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12984:ℝ)) (by norm_num [em12984]) ?_)
      (show bm12984^8 ≤ scalar12984.lowerTail by norm_num [bm12984, scalar12984])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12984, bm12984, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12984 :
    agent12984.root+dsL+scalar12984.worldRadius < √(1/100/aL) ∧
    2*(agent12984.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12984, agent12984, scalar12984, tp12984, tm12984, ep12984, em12984, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12984, agent12984, scalar12984, tp12984, tm12984, ep12984, em12984, dsL]

noncomputable def master12984 : MasterCertificate 12984 world12984 agent12984 :=
  master scalar12984 dsL tp12984 tm12984 ep12984 em12984
    (by norm_num [dsL]) (by norm_num [tp12984]) (by norm_num [tm12984])
    (by norm_num [ep12984]) (by norm_num [em12984])
    positive12984 negative12984 tails12984.1 tails12984.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12984.1 tailGuards12984.2

theorem preserves12984 : master12984.toScalarCertificate = scalar12984 := rfl

noncomputable def tp12985 : ℝ := (292686657 / 1250000000)
noncomputable def tm12985 : ℝ := (-((611813247 / 1000000000)))
noncomputable def ep12985 : ℝ := (13040855963606921 / 25000000000000000000)
noncomputable def em12985 : ℝ := (50749971941276367 / 100000000000000000000)
noncomputable def bp12985 : ℝ := (2680233426877920891 / 6250000000000000000)
noncomputable def bm12985 : ℝ := (21939474949374930433 / 50000000000000000000)

theorem positive12985 :
    Eplus aL (agent12985.root+dsL) scalar12985.worldRadius world12985.frame
      agent12985.frame tp12985 ≤ -ep12985 := by
  apply positive_check (eT := (115671824296143501161 / 100000000000000000000)) (y := (9513135462911146639 / 25000000000000000000)) (u := (73152655135584991493 / 50000000000000000000))
  · norm_num [world12985, agent12985, scalar12985, tp12985, tm12985, ep12985, em12985, dsL]
  · norm_num [world12985, agent12985, scalar12985, tp12985, tm12985, ep12985, em12985, dsL]
  · norm_num [world12985, agent12985, scalar12985, tp12985, tm12985, ep12985, em12985, dsL]
  · norm_num [world12985, agent12985, scalar12985, tp12985, tm12985, ep12985, em12985, dsL]
  · norm_num [world12985, agent12985, scalar12985, tp12985, tm12985, ep12985, em12985, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12985, agent12985, tp12985, tm12985, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12985, agent12985, scalar12985, tp12985, tm12985, ep12985, em12985, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12985, agent12985, tp12985, tm12985, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12985, agent12985, scalar12985, tp12985, tm12985, ep12985, em12985, dsL]

theorem negative12985 :
    Eminus aL (agent12985.root+dsL) scalar12985.worldRadius world12985.frame
      agent12985.frame tm12985 ≤ -em12985 := by
  apply negative_check (lo := (17089582129946973937 / 25000000000000000000)) (hi := (68358328519787895749 / 100000000000000000000))
    (y := (-((71638818992275907951 / 100000000000000000000)))) (u := (24425674568621935127 / 50000000000000000000))
  · norm_num [world12985, agent12985, scalar12985, tp12985, tm12985, ep12985, em12985, dsL]
  · norm_num [world12985, agent12985, scalar12985, tp12985, tm12985, ep12985, em12985, dsL]
  · norm_num [world12985, agent12985, scalar12985, tp12985, tm12985, ep12985, em12985, dsL]
  · norm_num [world12985, agent12985, scalar12985, tp12985, tm12985, ep12985, em12985, dsL]
  · norm_num [world12985, agent12985, scalar12985, tp12985, tm12985, ep12985, em12985, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12985, agent12985, tp12985, tm12985, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12985, agent12985, tp12985, tm12985, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12985, agent12985, scalar12985, tp12985, tm12985, ep12985, em12985, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12985, agent12985, tp12985, tm12985, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12985, agent12985, scalar12985, tp12985, tm12985, ep12985, em12985, dsL]

theorem tails12985 :
    exp (-((12985:ℝ)*ep12985)) ≤ scalar12985.upperTail ∧
    exp (-((12985:ℝ)*em12985)) ≤ scalar12985.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12985:ℝ)) (by norm_num [ep12985]) ?_)
      (show bp12985^8 ≤ scalar12985.upperTail by norm_num [bp12985, scalar12985])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12985, bp12985, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12985:ℝ)) (by norm_num [em12985]) ?_)
      (show bm12985^8 ≤ scalar12985.lowerTail by norm_num [bm12985, scalar12985])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12985, bm12985, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12985 :
    agent12985.root+dsL+scalar12985.worldRadius < √(1/100/aL) ∧
    2*(agent12985.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12985, agent12985, scalar12985, tp12985, tm12985, ep12985, em12985, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12985, agent12985, scalar12985, tp12985, tm12985, ep12985, em12985, dsL]

noncomputable def master12985 : MasterCertificate 12985 world12985 agent12985 :=
  master scalar12985 dsL tp12985 tm12985 ep12985 em12985
    (by norm_num [dsL]) (by norm_num [tp12985]) (by norm_num [tm12985])
    (by norm_num [ep12985]) (by norm_num [em12985])
    positive12985 negative12985 tails12985.1 tails12985.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12985.1 tailGuards12985.2

theorem preserves12985 : master12985.toScalarCertificate = scalar12985 := rfl

noncomputable def tp12986 : ℝ := (2341569313 / 10000000000)
noncomputable def tm12986 : ℝ := (-((6118294397 / 10000000000)))
noncomputable def ep12986 : ℝ := (13041430103172879 / 25000000000000000000)
noncomputable def em12986 : ℝ := (25375962702313969 / 50000000000000000000)
noncomputable def bp12986 : ℝ := (42879340194501947069 / 100000000000000000000)
noncomputable def bm12986 : ℝ := (43874775144335548519 / 100000000000000000000)

theorem positive12986 :
    Eplus aL (agent12986.root+dsL) scalar12986.worldRadius world12986.frame
      agent12986.frame tp12986 ≤ -ep12986 := by
  apply positive_check (eT := (115672012925660385797 / 100000000000000000000)) (y := (38053230976640121557 / 100000000000000000000)) (u := (146306318501106834919 / 100000000000000000000))
  · norm_num [world12986, agent12986, scalar12986, tp12986, tm12986, ep12986, em12986, dsL]
  · norm_num [world12986, agent12986, scalar12986, tp12986, tm12986, ep12986, em12986, dsL]
  · norm_num [world12986, agent12986, scalar12986, tp12986, tm12986, ep12986, em12986, dsL]
  · norm_num [world12986, agent12986, scalar12986, tp12986, tm12986, ep12986, em12986, dsL]
  · norm_num [world12986, agent12986, scalar12986, tp12986, tm12986, ep12986, em12986, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12986, agent12986, tp12986, tm12986, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12986, agent12986, scalar12986, tp12986, tm12986, ep12986, em12986, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12986, agent12986, tp12986, tm12986, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12986, agent12986, scalar12986, tp12986, tm12986, ep12986, em12986, dsL]

theorem negative12986 :
    Eminus aL (agent12986.root+dsL) scalar12986.worldRadius world12986.frame
      agent12986.frame tm12986 ≤ -em12986 := by
  apply negative_check (lo := (8544774208990388357 / 12500000000000000000)) (hi := (68358193671923106857 / 100000000000000000000))
    (y := (-((17909693441222892137 / 25000000000000000000)))) (u := (48851371231436295851 / 100000000000000000000))
  · norm_num [world12986, agent12986, scalar12986, tp12986, tm12986, ep12986, em12986, dsL]
  · norm_num [world12986, agent12986, scalar12986, tp12986, tm12986, ep12986, em12986, dsL]
  · norm_num [world12986, agent12986, scalar12986, tp12986, tm12986, ep12986, em12986, dsL]
  · norm_num [world12986, agent12986, scalar12986, tp12986, tm12986, ep12986, em12986, dsL]
  · norm_num [world12986, agent12986, scalar12986, tp12986, tm12986, ep12986, em12986, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12986, agent12986, tp12986, tm12986, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12986, agent12986, tp12986, tm12986, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12986, agent12986, scalar12986, tp12986, tm12986, ep12986, em12986, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12986, agent12986, tp12986, tm12986, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12986, agent12986, scalar12986, tp12986, tm12986, ep12986, em12986, dsL]

theorem tails12986 :
    exp (-((12986:ℝ)*ep12986)) ≤ scalar12986.upperTail ∧
    exp (-((12986:ℝ)*em12986)) ≤ scalar12986.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12986:ℝ)) (by norm_num [ep12986]) ?_)
      (show bp12986^8 ≤ scalar12986.upperTail by norm_num [bp12986, scalar12986])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12986, bp12986, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12986:ℝ)) (by norm_num [em12986]) ?_)
      (show bm12986^8 ≤ scalar12986.lowerTail by norm_num [bm12986, scalar12986])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12986, bm12986, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12986 :
    agent12986.root+dsL+scalar12986.worldRadius < √(1/100/aL) ∧
    2*(agent12986.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12986, agent12986, scalar12986, tp12986, tm12986, ep12986, em12986, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12986, agent12986, scalar12986, tp12986, tm12986, ep12986, em12986, dsL]

noncomputable def master12986 : MasterCertificate 12986 world12986 agent12986 :=
  master scalar12986 dsL tp12986 tm12986 ep12986 em12986
    (by norm_num [dsL]) (by norm_num [tp12986]) (by norm_num [tm12986])
    (by norm_num [ep12986]) (by norm_num [em12986])
    positive12986 negative12986 tails12986.1 tails12986.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12986.1 tailGuards12986.2

theorem preserves12986 : master12986.toScalarCertificate = scalar12986 := rfl

noncomputable def tp12987 : ℝ := (2341645377 / 10000000000)
noncomputable def tm12987 : ℝ := (-((764807021 / 1250000000)))
noncomputable def ep12987 : ℝ := (52168016372214857 / 100000000000000000000)
noncomputable def em12987 : ℝ := (2030155132814869 / 4000000000000000000)
noncomputable def bp12987 : ℝ := (21437473089942123903 / 50000000000000000000)
noncomputable def bm12987 : ℝ := (43870600962866618913 / 100000000000000000000)

theorem positive12987 :
    Eplus aL (agent12987.root+dsL) scalar12987.worldRadius world12987.frame
      agent12987.frame tp12987 ≤ -ep12987 := by
  apply positive_check (eT := (23134440327701334421 / 20000000000000000000)) (y := (7610784090000457379 / 20000000000000000000)) (u := (146307327247677580281 / 100000000000000000000))
  · norm_num [world12987, agent12987, scalar12987, tp12987, tm12987, ep12987, em12987, dsL]
  · norm_num [world12987, agent12987, scalar12987, tp12987, tm12987, ep12987, em12987, dsL]
  · norm_num [world12987, agent12987, scalar12987, tp12987, tm12987, ep12987, em12987, dsL]
  · norm_num [world12987, agent12987, scalar12987, tp12987, tm12987, ep12987, em12987, dsL]
  · norm_num [world12987, agent12987, scalar12987, tp12987, tm12987, ep12987, em12987, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12987, agent12987, tp12987, tm12987, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12987, agent12987, scalar12987, tp12987, tm12987, ep12987, em12987, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12987, agent12987, tp12987, tm12987, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12987, agent12987, scalar12987, tp12987, tm12987, ep12987, em12987, dsL]

theorem negative12987 :
    Eminus aL (agent12987.root+dsL) scalar12987.worldRadius world12987.frame
      agent12987.frame tm12987 ≤ -em12987 := by
  apply negative_check (lo := (68358059430224663329 / 100000000000000000000)) (hi := (6835805943022466333 / 10000000000000000000))
    (y := (-((71638727644919354853 / 100000000000000000000)))) (u := (48851393761680329269 / 100000000000000000000))
  · norm_num [world12987, agent12987, scalar12987, tp12987, tm12987, ep12987, em12987, dsL]
  · norm_num [world12987, agent12987, scalar12987, tp12987, tm12987, ep12987, em12987, dsL]
  · norm_num [world12987, agent12987, scalar12987, tp12987, tm12987, ep12987, em12987, dsL]
  · norm_num [world12987, agent12987, scalar12987, tp12987, tm12987, ep12987, em12987, dsL]
  · norm_num [world12987, agent12987, scalar12987, tp12987, tm12987, ep12987, em12987, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12987, agent12987, tp12987, tm12987, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12987, agent12987, tp12987, tm12987, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12987, agent12987, scalar12987, tp12987, tm12987, ep12987, em12987, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12987, agent12987, tp12987, tm12987, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12987, agent12987, scalar12987, tp12987, tm12987, ep12987, em12987, dsL]

theorem tails12987 :
    exp (-((12987:ℝ)*ep12987)) ≤ scalar12987.upperTail ∧
    exp (-((12987:ℝ)*em12987)) ≤ scalar12987.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12987:ℝ)) (by norm_num [ep12987]) ?_)
      (show bp12987^8 ≤ scalar12987.upperTail by norm_num [bp12987, scalar12987])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12987, bp12987, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12987:ℝ)) (by norm_num [em12987]) ?_)
      (show bm12987^8 ≤ scalar12987.lowerTail by norm_num [bm12987, scalar12987])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12987, bm12987, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12987 :
    agent12987.root+dsL+scalar12987.worldRadius < √(1/100/aL) ∧
    2*(agent12987.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12987, agent12987, scalar12987, tp12987, tm12987, ep12987, em12987, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12987, agent12987, scalar12987, tp12987, tm12987, ep12987, em12987, dsL]

noncomputable def master12987 : MasterCertificate 12987 world12987 agent12987 :=
  master scalar12987 dsL tp12987 tm12987 ep12987 em12987
    (by norm_num [dsL]) (by norm_num [tp12987]) (by norm_num [tm12987])
    (by norm_num [ep12987]) (by norm_num [em12987])
    positive12987 negative12987 tails12987.1 tails12987.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12987.1 tailGuards12987.2

theorem preserves12987 : master12987.toScalarCertificate = scalar12987 := rfl

noncomputable def tp12988 : ℝ := (234172141 / 1000000000)
noncomputable def tm12988 : ℝ := (-((3059308971 / 5000000000)))
noncomputable def ep12988 : ℝ := (52170310158905239 / 100000000000000000000)
noncomputable def em12988 : ℝ := (10151165842693189 / 20000000000000000000)
noncomputable def bp12988 : ℝ := (42870553881765065493 / 100000000000000000000)
noncomputable def bm12988 : ℝ := (43866428404827856509 / 100000000000000000000)

theorem positive12988 :
    Eplus aL (agent12988.root+dsL) scalar12988.worldRadius world12988.frame
      agent12988.frame tp12988 ≤ -ep12988 := by
  apply positive_check (eT := (115672390161373447343 / 100000000000000000000)) (y := (19027304953994471499 / 50000000000000000000)) (u := (36577083994676934201 / 25000000000000000000))
  · norm_num [world12988, agent12988, scalar12988, tp12988, tm12988, ep12988, em12988, dsL]
  · norm_num [world12988, agent12988, scalar12988, tp12988, tm12988, ep12988, em12988, dsL]
  · norm_num [world12988, agent12988, scalar12988, tp12988, tm12988, ep12988, em12988, dsL]
  · norm_num [world12988, agent12988, scalar12988, tp12988, tm12988, ep12988, em12988, dsL]
  · norm_num [world12988, agent12988, scalar12988, tp12988, tm12988, ep12988, em12988, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12988, agent12988, tp12988, tm12988, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12988, agent12988, scalar12988, tp12988, tm12988, ep12988, em12988, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12988, agent12988, tp12988, tm12988, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12988, agent12988, scalar12988, tp12988, tm12988, ep12988, em12988, dsL]

theorem negative12988 :
    Eminus aL (agent12988.root+dsL) scalar12988.worldRadius world12988.frame
      agent12988.frame tm12988 ≤ -em12988 := by
  apply negative_check (lo := (6835792511892916441 / 10000000000000000000)) (hi := (68357925118929164411 / 100000000000000000000))
    (y := (-((6995965045409469 / 9765625000000000)))) (u := (12212854007028680491 / 25000000000000000000))
  · norm_num [world12988, agent12988, scalar12988, tp12988, tm12988, ep12988, em12988, dsL]
  · norm_num [world12988, agent12988, scalar12988, tp12988, tm12988, ep12988, em12988, dsL]
  · norm_num [world12988, agent12988, scalar12988, tp12988, tm12988, ep12988, em12988, dsL]
  · norm_num [world12988, agent12988, scalar12988, tp12988, tm12988, ep12988, em12988, dsL]
  · norm_num [world12988, agent12988, scalar12988, tp12988, tm12988, ep12988, em12988, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12988, agent12988, tp12988, tm12988, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12988, agent12988, tp12988, tm12988, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12988, agent12988, scalar12988, tp12988, tm12988, ep12988, em12988, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12988, agent12988, tp12988, tm12988, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12988, agent12988, scalar12988, tp12988, tm12988, ep12988, em12988, dsL]

theorem tails12988 :
    exp (-((12988:ℝ)*ep12988)) ≤ scalar12988.upperTail ∧
    exp (-((12988:ℝ)*em12988)) ≤ scalar12988.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12988:ℝ)) (by norm_num [ep12988]) ?_)
      (show bp12988^8 ≤ scalar12988.upperTail by norm_num [bp12988, scalar12988])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12988, bp12988, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12988:ℝ)) (by norm_num [em12988]) ?_)
      (show bm12988^8 ≤ scalar12988.lowerTail by norm_num [bm12988, scalar12988])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12988, bm12988, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12988 :
    agent12988.root+dsL+scalar12988.worldRadius < √(1/100/aL) ∧
    2*(agent12988.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12988, agent12988, scalar12988, tp12988, tm12988, ep12988, em12988, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12988, agent12988, scalar12988, tp12988, tm12988, ep12988, em12988, dsL]

noncomputable def master12988 : MasterCertificate 12988 world12988 agent12988 :=
  master scalar12988 dsL tp12988 tm12988 ep12988 em12988
    (by norm_num [dsL]) (by norm_num [tp12988]) (by norm_num [tm12988])
    (by norm_num [ep12988]) (by norm_num [em12988])
    positive12988 negative12988 tails12988.1 tails12988.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12988.1 tailGuards12988.2

theorem preserves12988 : master12988.toScalarCertificate = scalar12988 := rfl

noncomputable def tp12989 : ℝ := (2341797421 / 10000000000)
noncomputable def tm12989 : ℝ := (-((1223755909 / 2000000000)))
noncomputable def ep12989 : ℝ := (26086301837677783 / 50000000000000000000)
noncomputable def em12989 : ℝ := (634472248085507 / 1250000000000000000)
noncomputable def bp12989 : ℝ := (4286616197588086719 / 10000000000000000000)
noncomputable def bm12989 : ℝ := (2741391013417411971 / 6250000000000000000)

theorem positive12989 :
    Eplus aL (agent12989.root+dsL) scalar12989.worldRadius world12989.frame
      agent12989.frame tp12989 ≤ -ep12989 := by
  apply positive_check (eT := (115672578559030545923 / 100000000000000000000)) (y := (19027649655300562799 / 50000000000000000000)) (u := (73154672317837332327 / 50000000000000000000))
  · norm_num [world12989, agent12989, scalar12989, tp12989, tm12989, ep12989, em12989, dsL]
  · norm_num [world12989, agent12989, scalar12989, tp12989, tm12989, ep12989, em12989, dsL]
  · norm_num [world12989, agent12989, scalar12989, tp12989, tm12989, ep12989, em12989, dsL]
  · norm_num [world12989, agent12989, scalar12989, tp12989, tm12989, ep12989, em12989, dsL]
  · norm_num [world12989, agent12989, scalar12989, tp12989, tm12989, ep12989, em12989, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12989, agent12989, tp12989, tm12989, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12989, agent12989, scalar12989, tp12989, tm12989, ep12989, em12989, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12989, agent12989, tp12989, tm12989, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12989, agent12989, scalar12989, tp12989, tm12989, ep12989, em12989, dsL]

theorem negative12989 :
    Eminus aL (agent12989.root+dsL) scalar12989.worldRadius world12989.frame
      agent12989.frame tm12989 ≤ -em12989 := by
  apply negative_check (lo := (17089447869368671693 / 25000000000000000000)) (hi := (68357791477474686773 / 100000000000000000000))
    (y := (-((17909658965518088781 / 25000000000000000000)))) (u := (48851438598900899223 / 100000000000000000000))
  · norm_num [world12989, agent12989, scalar12989, tp12989, tm12989, ep12989, em12989, dsL]
  · norm_num [world12989, agent12989, scalar12989, tp12989, tm12989, ep12989, em12989, dsL]
  · norm_num [world12989, agent12989, scalar12989, tp12989, tm12989, ep12989, em12989, dsL]
  · norm_num [world12989, agent12989, scalar12989, tp12989, tm12989, ep12989, em12989, dsL]
  · norm_num [world12989, agent12989, scalar12989, tp12989, tm12989, ep12989, em12989, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12989, agent12989, tp12989, tm12989, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12989, agent12989, tp12989, tm12989, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12989, agent12989, scalar12989, tp12989, tm12989, ep12989, em12989, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12989, agent12989, tp12989, tm12989, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12989, agent12989, scalar12989, tp12989, tm12989, ep12989, em12989, dsL]

theorem tails12989 :
    exp (-((12989:ℝ)*ep12989)) ≤ scalar12989.upperTail ∧
    exp (-((12989:ℝ)*em12989)) ≤ scalar12989.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12989:ℝ)) (by norm_num [ep12989]) ?_)
      (show bp12989^8 ≤ scalar12989.upperTail by norm_num [bp12989, scalar12989])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12989, bp12989, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12989:ℝ)) (by norm_num [em12989]) ?_)
      (show bm12989^8 ≤ scalar12989.lowerTail by norm_num [bm12989, scalar12989])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12989, bm12989, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12989 :
    agent12989.root+dsL+scalar12989.worldRadius < √(1/100/aL) ∧
    2*(agent12989.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12989, agent12989, scalar12989, tp12989, tm12989, ep12989, em12989, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12989, agent12989, scalar12989, tp12989, tm12989, ep12989, em12989, dsL]

noncomputable def master12989 : MasterCertificate 12989 world12989 agent12989 :=
  master scalar12989 dsL tp12989 tm12989 ep12989 em12989
    (by norm_num [dsL]) (by norm_num [tp12989]) (by norm_num [tm12989])
    (by norm_num [ep12989]) (by norm_num [em12989])
    positive12989 negative12989 tails12989.1 tails12989.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12989.1 tailGuards12989.2

theorem preserves12989 : master12989.toScalarCertificate = scalar12989 := rfl

noncomputable def tp12990 : ℝ := (2341945249 / 10000000000)
noncomputable def tm12990 : ℝ := (-((6119158907 / 10000000000)))
noncomputable def ep12990 : ℝ := (26088128297594017 / 50000000000000000000)
noncomputable def em12990 : ℝ := (25380607205355919 / 50000000000000000000)
noncomputable def bp12990 : ℝ := (42860824183363993787 / 100000000000000000000)
noncomputable def bm12990 : ℝ := (2741064215348045701 / 6250000000000000000)

theorem positive12990 :
    Eplus aL (agent12990.root+dsL) scalar12990.worldRadius world12990.frame
      agent12990.frame tp12990 ≤ -ep12990 := by
  apply positive_check (eT := (14459160432077161719 / 12500000000000000000)) (y := (19027635823076569269 / 50000000000000000000)) (u := (29261860832001543279 / 20000000000000000000))
  · norm_num [world12990, agent12990, scalar12990, tp12990, tm12990, ep12990, em12990, dsL]
  · norm_num [world12990, agent12990, scalar12990, tp12990, tm12990, ep12990, em12990, dsL]
  · norm_num [world12990, agent12990, scalar12990, tp12990, tm12990, ep12990, em12990, dsL]
  · norm_num [world12990, agent12990, scalar12990, tp12990, tm12990, ep12990, em12990, dsL]
  · norm_num [world12990, agent12990, scalar12990, tp12990, tm12990, ep12990, em12990, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12990, agent12990, tp12990, tm12990, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12990, agent12990, scalar12990, tp12990, tm12990, ep12990, em12990, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12990, agent12990, tp12990, tm12990, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12990, agent12990, scalar12990, tp12990, tm12990, ep12990, em12990, dsL]

theorem negative12990 :
    Eminus aL (agent12990.root+dsL) scalar12990.worldRadius world12990.frame
      agent12990.frame tm12990 ≤ -em12990 := by
  apply negative_check (lo := (8544591543655027 / 12500000000000000)) (hi := (68356732349240216001 / 100000000000000000000))
    (y := (-((71636717683740448431 / 100000000000000000000)))) (u := (24426187832799102241 / 50000000000000000000))
  · norm_num [world12990, agent12990, scalar12990, tp12990, tm12990, ep12990, em12990, dsL]
  · norm_num [world12990, agent12990, scalar12990, tp12990, tm12990, ep12990, em12990, dsL]
  · norm_num [world12990, agent12990, scalar12990, tp12990, tm12990, ep12990, em12990, dsL]
  · norm_num [world12990, agent12990, scalar12990, tp12990, tm12990, ep12990, em12990, dsL]
  · norm_num [world12990, agent12990, scalar12990, tp12990, tm12990, ep12990, em12990, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12990, agent12990, tp12990, tm12990, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12990, agent12990, tp12990, tm12990, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12990, agent12990, scalar12990, tp12990, tm12990, ep12990, em12990, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12990, agent12990, tp12990, tm12990, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12990, agent12990, scalar12990, tp12990, tm12990, ep12990, em12990, dsL]

theorem tails12990 :
    exp (-((12990:ℝ)*ep12990)) ≤ scalar12990.upperTail ∧
    exp (-((12990:ℝ)*em12990)) ≤ scalar12990.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12990:ℝ)) (by norm_num [ep12990]) ?_)
      (show bp12990^8 ≤ scalar12990.upperTail by norm_num [bp12990, scalar12990])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12990, bp12990, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12990:ℝ)) (by norm_num [em12990]) ?_)
      (show bm12990^8 ≤ scalar12990.lowerTail by norm_num [bm12990, scalar12990])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12990, bm12990, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12990 :
    agent12990.root+dsL+scalar12990.worldRadius < √(1/100/aL) ∧
    2*(agent12990.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12990, agent12990, scalar12990, tp12990, tm12990, ep12990, em12990, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12990, agent12990, scalar12990, tp12990, tm12990, ep12990, em12990, dsL]

noncomputable def master12990 : MasterCertificate 12990 world12990 agent12990 :=
  master scalar12990 dsL tp12990 tm12990 ep12990 em12990
    (by norm_num [dsL]) (by norm_num [tp12990]) (by norm_num [tm12990])
    (by norm_num [ep12990]) (by norm_num [em12990])
    positive12990 negative12990 tails12990.1 tails12990.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12990.1 tailGuards12990.2

theorem preserves12990 : master12990.toScalarCertificate = scalar12990 := rfl

noncomputable def tp12991 : ℝ := (585505289 / 2500000000)
noncomputable def tm12991 : ℝ := (-((6119320313 / 10000000000)))
noncomputable def ep12991 : ℝ := (10435709484714693 / 20000000000000000000)
noncomputable def em12991 : ℝ := (50763162554066343 / 100000000000000000000)
noncomputable def bp12991 : ℝ := (21428217290340285029 / 50000000000000000000)
noncomputable def bm12991 : ℝ := (43852857413690945381 / 100000000000000000000)

theorem positive12991 :
    Eplus aL (agent12991.root+dsL) scalar12991.worldRadius world12991.frame
      agent12991.frame tp12991 ≤ -ep12991 := by
  apply positive_check (eT := (57836735581096954007 / 50000000000000000000)) (y := (38055959913826317821 / 100000000000000000000)) (u := (73155155581558268869 / 50000000000000000000))
  · norm_num [world12991, agent12991, scalar12991, tp12991, tm12991, ep12991, em12991, dsL]
  · norm_num [world12991, agent12991, scalar12991, tp12991, tm12991, ep12991, em12991, dsL]
  · norm_num [world12991, agent12991, scalar12991, tp12991, tm12991, ep12991, em12991, dsL]
  · norm_num [world12991, agent12991, scalar12991, tp12991, tm12991, ep12991, em12991, dsL]
  · norm_num [world12991, agent12991, scalar12991, tp12991, tm12991, ep12991, em12991, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12991, agent12991, tp12991, tm12991, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12991, agent12991, scalar12991, tp12991, tm12991, ep12991, em12991, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12991, agent12991, tp12991, tm12991, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12991, agent12991, scalar12991, tp12991, tm12991, ep12991, em12991, dsL]

theorem negative12991 :
    Eminus aL (agent12991.root+dsL) scalar12991.worldRadius world12991.frame
      agent12991.frame tm12991 ≤ -em12991 := by
  apply negative_check (lo := (34178299726354496489 / 50000000000000000000)) (hi := (68356599452708992979 / 100000000000000000000))
    (y := (-((35818335307291906501 / 50000000000000000000)))) (u := (48852398660004838287 / 100000000000000000000))
  · norm_num [world12991, agent12991, scalar12991, tp12991, tm12991, ep12991, em12991, dsL]
  · norm_num [world12991, agent12991, scalar12991, tp12991, tm12991, ep12991, em12991, dsL]
  · norm_num [world12991, agent12991, scalar12991, tp12991, tm12991, ep12991, em12991, dsL]
  · norm_num [world12991, agent12991, scalar12991, tp12991, tm12991, ep12991, em12991, dsL]
  · norm_num [world12991, agent12991, scalar12991, tp12991, tm12991, ep12991, em12991, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12991, agent12991, tp12991, tm12991, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12991, agent12991, tp12991, tm12991, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12991, agent12991, scalar12991, tp12991, tm12991, ep12991, em12991, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12991, agent12991, tp12991, tm12991, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12991, agent12991, scalar12991, tp12991, tm12991, ep12991, em12991, dsL]

theorem tails12991 :
    exp (-((12991:ℝ)*ep12991)) ≤ scalar12991.upperTail ∧
    exp (-((12991:ℝ)*em12991)) ≤ scalar12991.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12991:ℝ)) (by norm_num [ep12991]) ?_)
      (show bp12991^8 ≤ scalar12991.upperTail by norm_num [bp12991, scalar12991])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12991, bp12991, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12991:ℝ)) (by norm_num [em12991]) ?_)
      (show bm12991^8 ≤ scalar12991.lowerTail by norm_num [bm12991, scalar12991])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12991, bm12991, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12991 :
    agent12991.root+dsL+scalar12991.worldRadius < √(1/100/aL) ∧
    2*(agent12991.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12991, agent12991, scalar12991, tp12991, tm12991, ep12991, em12991, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12991, agent12991, scalar12991, tp12991, tm12991, ep12991, em12991, dsL]

noncomputable def master12991 : MasterCertificate 12991 world12991 agent12991 :=
  master scalar12991 dsL tp12991 tm12991 ep12991 em12991
    (by norm_num [dsL]) (by norm_num [tp12991]) (by norm_num [tm12991])
    (by norm_num [ep12991]) (by norm_num [em12991])
    positive12991 negative12991 tails12991.1 tails12991.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12991.1 tailGuards12991.2

theorem preserves12991 : master12991.toScalarCertificate = scalar12991 := rfl

noncomputable def tp12992 : ℝ := (585524251 / 2500000000)
noncomputable def tm12992 : ℝ := (-((6119481523 / 10000000000)))
noncomputable def ep12992 : ℝ := (52180836704265331 / 100000000000000000000)
noncomputable def em12992 : ℝ := (50765109270499801 / 100000000000000000000)
noncomputable def bp12992 : ℝ := (2142602312960468637 / 5000000000000000000)
noncomputable def bm12992 : ℝ := (1096217214521633497 / 2500000000000000000)

theorem positive12992 :
    Eplus aL (agent12992.root+dsL) scalar12992.worldRadius world12992.frame
      agent12992.frame tp12992 ≤ -ep12992 := by
  apply positive_check (eT := (28918414619124115603 / 25000000000000000000)) (y := (19028323737695107711 / 50000000000000000000)) (u := (146311317140038465673 / 100000000000000000000))
  · norm_num [world12992, agent12992, scalar12992, tp12992, tm12992, ep12992, em12992, dsL]
  · norm_num [world12992, agent12992, scalar12992, tp12992, tm12992, ep12992, em12992, dsL]
  · norm_num [world12992, agent12992, scalar12992, tp12992, tm12992, ep12992, em12992, dsL]
  · norm_num [world12992, agent12992, scalar12992, tp12992, tm12992, ep12992, em12992, dsL]
  · norm_num [world12992, agent12992, scalar12992, tp12992, tm12992, ep12992, em12992, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12992, agent12992, tp12992, tm12992, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12992, agent12992, scalar12992, tp12992, tm12992, ep12992, em12992, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12992, agent12992, tp12992, tm12992, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12992, agent12992, scalar12992, tp12992, tm12992, ep12992, em12992, dsL]

theorem negative12992 :
    Eminus aL (agent12992.root+dsL) scalar12992.worldRadius world12992.frame
      agent12992.frame tm12992 ≤ -em12992 := by
  apply negative_check (lo := (34178233666093273239 / 50000000000000000000)) (hi := (68356467332186546479 / 100000000000000000000))
    (y := (-((14327324402295772673 / 20000000000000000000)))) (u := (48852422403793199533 / 100000000000000000000))
  · norm_num [world12992, agent12992, scalar12992, tp12992, tm12992, ep12992, em12992, dsL]
  · norm_num [world12992, agent12992, scalar12992, tp12992, tm12992, ep12992, em12992, dsL]
  · norm_num [world12992, agent12992, scalar12992, tp12992, tm12992, ep12992, em12992, dsL]
  · norm_num [world12992, agent12992, scalar12992, tp12992, tm12992, ep12992, em12992, dsL]
  · norm_num [world12992, agent12992, scalar12992, tp12992, tm12992, ep12992, em12992, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12992, agent12992, tp12992, tm12992, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12992, agent12992, tp12992, tm12992, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12992, agent12992, scalar12992, tp12992, tm12992, ep12992, em12992, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12992, agent12992, tp12992, tm12992, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12992, agent12992, scalar12992, tp12992, tm12992, ep12992, em12992, dsL]

theorem tails12992 :
    exp (-((12992:ℝ)*ep12992)) ≤ scalar12992.upperTail ∧
    exp (-((12992:ℝ)*em12992)) ≤ scalar12992.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12992:ℝ)) (by norm_num [ep12992]) ?_)
      (show bp12992^8 ≤ scalar12992.upperTail by norm_num [bp12992, scalar12992])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12992, bp12992, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12992:ℝ)) (by norm_num [em12992]) ?_)
      (show bm12992^8 ≤ scalar12992.lowerTail by norm_num [bm12992, scalar12992])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12992, bm12992, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12992 :
    agent12992.root+dsL+scalar12992.worldRadius < √(1/100/aL) ∧
    2*(agent12992.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12992, agent12992, scalar12992, tp12992, tm12992, ep12992, em12992, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12992, agent12992, scalar12992, tp12992, tm12992, ep12992, em12992, dsL]

noncomputable def master12992 : MasterCertificate 12992 world12992 agent12992 :=
  master scalar12992 dsL tp12992 tm12992 ep12992 em12992
    (by norm_num [dsL]) (by norm_num [tp12992]) (by norm_num [tm12992])
    (by norm_num [ep12992]) (by norm_num [em12992])
    positive12992 negative12992 tails12992.1 tails12992.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12992.1 tailGuards12992.2

theorem preserves12992 : master12992.toScalarCertificate = scalar12992 := rfl

noncomputable def tp12993 : ℝ := (36596451 / 156250000)
noncomputable def tm12993 : ℝ := (-((244785717 / 400000000)))
noncomputable def ep12993 : ℝ := (52183125247445767 / 100000000000000000000)
noncomputable def em12993 : ℝ := (50767055293753871 / 100000000000000000000)
noncomputable def bp12993 : ℝ := (42847658655092193053 / 100000000000000000000)
noncomputable def bm12993 : ℝ := (5480565053071246893 / 12500000000000000000)

theorem positive12993 :
    Eplus aL (agent12993.root+dsL) scalar12993.worldRadius world12993.frame
      agent12993.frame tp12993 ≤ -ep12993 := by
  apply positive_check (eT := (115673845910091053543 / 100000000000000000000)) (y := (38057335624095834421 / 100000000000000000000)) (u := (146312323982937823173 / 100000000000000000000))
  · norm_num [world12993, agent12993, scalar12993, tp12993, tm12993, ep12993, em12993, dsL]
  · norm_num [world12993, agent12993, scalar12993, tp12993, tm12993, ep12993, em12993, dsL]
  · norm_num [world12993, agent12993, scalar12993, tp12993, tm12993, ep12993, em12993, dsL]
  · norm_num [world12993, agent12993, scalar12993, tp12993, tm12993, ep12993, em12993, dsL]
  · norm_num [world12993, agent12993, scalar12993, tp12993, tm12993, ep12993, em12993, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12993, agent12993, tp12993, tm12993, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12993, agent12993, scalar12993, tp12993, tm12993, ep12993, em12993, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12993, agent12993, tp12993, tm12993, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12993, agent12993, scalar12993, tp12993, tm12993, ep12993, em12993, dsL]

theorem negative12993 :
    Eminus aL (agent12993.root+dsL) scalar12993.worldRadius world12993.frame
      agent12993.frame tm12993 ≤ -em12993 := by
  apply negative_check (lo := (68356334338857895307 / 100000000000000000000)) (hi := (17089083584714473827 / 25000000000000000000))
    (y := (-((71636576149165017 / 100000000000000000)))) (u := (9770488961729924321 / 20000000000000000000))
  · norm_num [world12993, agent12993, scalar12993, tp12993, tm12993, ep12993, em12993, dsL]
  · norm_num [world12993, agent12993, scalar12993, tp12993, tm12993, ep12993, em12993, dsL]
  · norm_num [world12993, agent12993, scalar12993, tp12993, tm12993, ep12993, em12993, dsL]
  · norm_num [world12993, agent12993, scalar12993, tp12993, tm12993, ep12993, em12993, dsL]
  · norm_num [world12993, agent12993, scalar12993, tp12993, tm12993, ep12993, em12993, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12993, agent12993, tp12993, tm12993, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12993, agent12993, tp12993, tm12993, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12993, agent12993, scalar12993, tp12993, tm12993, ep12993, em12993, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12993, agent12993, tp12993, tm12993, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12993, agent12993, scalar12993, tp12993, tm12993, ep12993, em12993, dsL]

theorem tails12993 :
    exp (-((12993:ℝ)*ep12993)) ≤ scalar12993.upperTail ∧
    exp (-((12993:ℝ)*em12993)) ≤ scalar12993.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12993:ℝ)) (by norm_num [ep12993]) ?_)
      (show bp12993^8 ≤ scalar12993.upperTail by norm_num [bp12993, scalar12993])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12993, bp12993, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12993:ℝ)) (by norm_num [em12993]) ?_)
      (show bm12993^8 ≤ scalar12993.lowerTail by norm_num [bm12993, scalar12993])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12993, bm12993, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12993 :
    agent12993.root+dsL+scalar12993.worldRadius < √(1/100/aL) ∧
    2*(agent12993.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12993, agent12993, scalar12993, tp12993, tm12993, ep12993, em12993, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12993, agent12993, scalar12993, tp12993, tm12993, ep12993, em12993, dsL]

noncomputable def master12993 : MasterCertificate 12993 world12993 agent12993 :=
  master scalar12993 dsL tp12993 tm12993 ep12993 em12993
    (by norm_num [dsL]) (by norm_num [tp12993]) (by norm_num [tm12993])
    (by norm_num [ep12993]) (by norm_num [em12993])
    positive12993 negative12993 tails12993.1 tails12993.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12993.1 tailGuards12993.2

theorem preserves12993 : master12993.toScalarCertificate = scalar12993 := rfl

noncomputable def tp12994 : ℝ := (468449739 / 2000000000)
noncomputable def tm12994 : ℝ := (-((611980419 / 1000000000)))
noncomputable def ep12994 : ℝ := (10437082542105929 / 20000000000000000000)
noncomputable def em12994 : ℝ := (50769000324044487 / 100000000000000000000)
noncomputable def bp12994 : ℝ := (8568654401343591369 / 20000000000000000000)
noncomputable def bm12994 : ℝ := (43840353158270542657 / 100000000000000000000)

theorem positive12994 :
    Eplus aL (agent12994.root+dsL) scalar12994.worldRadius world12994.frame
      agent12994.frame tp12994 ≤ -ep12994 := by
  apply positive_check (eT := (115674033168152056267 / 100000000000000000000)) (y := (7611604708185271099 / 20000000000000000000)) (u := (7315666524675080107 / 5000000000000000000))
  · norm_num [world12994, agent12994, scalar12994, tp12994, tm12994, ep12994, em12994, dsL]
  · norm_num [world12994, agent12994, scalar12994, tp12994, tm12994, ep12994, em12994, dsL]
  · norm_num [world12994, agent12994, scalar12994, tp12994, tm12994, ep12994, em12994, dsL]
  · norm_num [world12994, agent12994, scalar12994, tp12994, tm12994, ep12994, em12994, dsL]
  · norm_num [world12994, agent12994, scalar12994, tp12994, tm12994, ep12994, em12994, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12994, agent12994, tp12994, tm12994, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12994, agent12994, scalar12994, tp12994, tm12994, ep12994, em12994, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12994, agent12994, tp12994, tm12994, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12994, agent12994, scalar12994, tp12994, tm12994, ep12994, em12994, dsL]

theorem negative12994 :
    Eminus aL (agent12994.root+dsL) scalar12994.worldRadius world12994.frame
      agent12994.frame tm12994 ≤ -em12994 := by
  apply negative_check (lo := (68356201870814819129 / 100000000000000000000)) (hi := (6835620187081481913 / 10000000000000000000))
    (y := (-((4477283090480877789 / 6250000000000000000)))) (u := (48852467623465280639 / 100000000000000000000))
  · norm_num [world12994, agent12994, scalar12994, tp12994, tm12994, ep12994, em12994, dsL]
  · norm_num [world12994, agent12994, scalar12994, tp12994, tm12994, ep12994, em12994, dsL]
  · norm_num [world12994, agent12994, scalar12994, tp12994, tm12994, ep12994, em12994, dsL]
  · norm_num [world12994, agent12994, scalar12994, tp12994, tm12994, ep12994, em12994, dsL]
  · norm_num [world12994, agent12994, scalar12994, tp12994, tm12994, ep12994, em12994, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12994, agent12994, tp12994, tm12994, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12994, agent12994, tp12994, tm12994, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12994, agent12994, scalar12994, tp12994, tm12994, ep12994, em12994, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12994, agent12994, tp12994, tm12994, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12994, agent12994, scalar12994, tp12994, tm12994, ep12994, em12994, dsL]

theorem tails12994 :
    exp (-((12994:ℝ)*ep12994)) ≤ scalar12994.upperTail ∧
    exp (-((12994:ℝ)*em12994)) ≤ scalar12994.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12994:ℝ)) (by norm_num [ep12994]) ?_)
      (show bp12994^8 ≤ scalar12994.upperTail by norm_num [bp12994, scalar12994])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12994, bp12994, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12994:ℝ)) (by norm_num [em12994]) ?_)
      (show bm12994^8 ≤ scalar12994.lowerTail by norm_num [bm12994, scalar12994])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12994, bm12994, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12994 :
    agent12994.root+dsL+scalar12994.worldRadius < √(1/100/aL) ∧
    2*(agent12994.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12994, agent12994, scalar12994, tp12994, tm12994, ep12994, em12994, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12994, agent12994, scalar12994, tp12994, tm12994, ep12994, em12994, dsL]

noncomputable def master12994 : MasterCertificate 12994 world12994 agent12994 :=
  master scalar12994 dsL tp12994 tm12994 ep12994 em12994
    (by norm_num [dsL]) (by norm_num [tp12994]) (by norm_num [tm12994])
    (by norm_num [ep12994]) (by norm_num [em12994])
    positive12994 negative12994 tails12994.1 tails12994.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12994.1 tailGuards12994.2

theorem preserves12994 : master12994.toScalarCertificate = scalar12994 := rfl

noncomputable def tp12995 : ℝ := (1171162227 / 5000000000)
noncomputable def tm12995 : ℝ := (-((3059982593 / 5000000000)))
noncomputable def ep12995 : ℝ := (10437539791842551 / 20000000000000000000)
noncomputable def em12995 : ℝ := (25385472109709529 / 50000000000000000000)
noncomputable def bp12995 : ℝ := (42838886407516103017 / 100000000000000000000)
noncomputable def bm12995 : ℝ := (5479523360378893759 / 12500000000000000000)

theorem positive12995 :
    Eplus aL (agent12995.root+dsL) scalar12995.worldRadius world12995.frame
      agent12995.frame tp12995 ≤ -ep12995 := by
  apply positive_check (eT := (115674219941468429837 / 100000000000000000000)) (y := (7611742125459159747 / 20000000000000000000)) (u := (146314335795905745369 / 100000000000000000000))
  · norm_num [world12995, agent12995, scalar12995, tp12995, tm12995, ep12995, em12995, dsL]
  · norm_num [world12995, agent12995, scalar12995, tp12995, tm12995, ep12995, em12995, dsL]
  · norm_num [world12995, agent12995, scalar12995, tp12995, tm12995, ep12995, em12995, dsL]
  · norm_num [world12995, agent12995, scalar12995, tp12995, tm12995, ep12995, em12995, dsL]
  · norm_num [world12995, agent12995, scalar12995, tp12995, tm12995, ep12995, em12995, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12995, agent12995, tp12995, tm12995, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12995, agent12995, scalar12995, tp12995, tm12995, ep12995, em12995, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12995, agent12995, tp12995, tm12995, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12995, agent12995, scalar12995, tp12995, tm12995, ep12995, em12995, dsL]

theorem negative12995 :
    Eminus aL (agent12995.root+dsL) scalar12995.worldRadius world12995.frame
      agent12995.frame tm12995 ≤ -em12995 := by
  apply negative_check (lo := (68356070488955488289 / 100000000000000000000)) (hi := (6835607048895548829 / 10000000000000000000))
    (y := (-((71636480923845064643 / 100000000000000000000)))) (u := (48852491328568644557 / 100000000000000000000))
  · norm_num [world12995, agent12995, scalar12995, tp12995, tm12995, ep12995, em12995, dsL]
  · norm_num [world12995, agent12995, scalar12995, tp12995, tm12995, ep12995, em12995, dsL]
  · norm_num [world12995, agent12995, scalar12995, tp12995, tm12995, ep12995, em12995, dsL]
  · norm_num [world12995, agent12995, scalar12995, tp12995, tm12995, ep12995, em12995, dsL]
  · norm_num [world12995, agent12995, scalar12995, tp12995, tm12995, ep12995, em12995, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12995, agent12995, tp12995, tm12995, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12995, agent12995, tp12995, tm12995, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12995, agent12995, scalar12995, tp12995, tm12995, ep12995, em12995, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12995, agent12995, tp12995, tm12995, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12995, agent12995, scalar12995, tp12995, tm12995, ep12995, em12995, dsL]

theorem tails12995 :
    exp (-((12995:ℝ)*ep12995)) ≤ scalar12995.upperTail ∧
    exp (-((12995:ℝ)*em12995)) ≤ scalar12995.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12995:ℝ)) (by norm_num [ep12995]) ?_)
      (show bp12995^8 ≤ scalar12995.upperTail by norm_num [bp12995, scalar12995])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12995, bp12995, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12995:ℝ)) (by norm_num [em12995]) ?_)
      (show bm12995^8 ≤ scalar12995.lowerTail by norm_num [bm12995, scalar12995])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12995, bm12995, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12995 :
    agent12995.root+dsL+scalar12995.worldRadius < √(1/100/aL) ∧
    2*(agent12995.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12995, agent12995, scalar12995, tp12995, tm12995, ep12995, em12995, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12995, agent12995, scalar12995, tp12995, tm12995, ep12995, em12995, dsL]

noncomputable def master12995 : MasterCertificate 12995 world12995 agent12995 :=
  master scalar12995 dsL tp12995 tm12995 ep12995 em12995
    (by norm_num [dsL]) (by norm_num [tp12995]) (by norm_num [tm12995])
    (by norm_num [ep12995]) (by norm_num [em12995])
    positive12995 negative12995 tails12995.1 tails12995.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12995.1 tailGuards12995.2

theorem preserves12995 : master12995.toScalarCertificate = scalar12995 := rfl

noncomputable def tp12996 : ℝ := (2342400189 / 10000000000)
noncomputable def tm12996 : ℝ := (-((95626971 / 156250000)))
noncomputable def ep12996 : ℝ := (652374786079671 / 1250000000000000000)
noncomputable def em12996 : ℝ := (25386442996657179 / 50000000000000000000)
noncomputable def bp12996 : ℝ := (42834502627837995009 / 100000000000000000000)
noncomputable def bm12996 : ℝ := (8766404460262919187 / 20000000000000000000)

theorem positive12996 :
    Eplus aL (agent12996.root+dsL) scalar12996.worldRadius world12996.frame
      agent12996.frame tp12996 ≤ -ep12996 := by
  apply positive_check (eT := (5783720328761250057 / 5000000000000000000)) (y := (38059397666533404453 / 100000000000000000000)) (u := (4572354407383003103 / 3125000000000000000))
  · norm_num [world12996, agent12996, scalar12996, tp12996, tm12996, ep12996, em12996, dsL]
  · norm_num [world12996, agent12996, scalar12996, tp12996, tm12996, ep12996, em12996, dsL]
  · norm_num [world12996, agent12996, scalar12996, tp12996, tm12996, ep12996, em12996, dsL]
  · norm_num [world12996, agent12996, scalar12996, tp12996, tm12996, ep12996, em12996, dsL]
  · norm_num [world12996, agent12996, scalar12996, tp12996, tm12996, ep12996, em12996, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12996, agent12996, tp12996, tm12996, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12996, agent12996, scalar12996, tp12996, tm12996, ep12996, em12996, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12996, agent12996, tp12996, tm12996, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12996, agent12996, scalar12996, tp12996, tm12996, ep12996, em12996, dsL]

theorem negative12996 :
    Eminus aL (agent12996.root+dsL) scalar12996.worldRadius world12996.frame
      agent12996.frame tm12996 ≤ -em12996 := by
  apply negative_check (lo := (68355939211635837499 / 100000000000000000000)) (hi := (5468475136930867 / 8000000000000000))
    (y := (-((71636432254138355889 / 100000000000000000000)))) (u := (12213128776234670009 / 25000000000000000000))
  · norm_num [world12996, agent12996, scalar12996, tp12996, tm12996, ep12996, em12996, dsL]
  · norm_num [world12996, agent12996, scalar12996, tp12996, tm12996, ep12996, em12996, dsL]
  · norm_num [world12996, agent12996, scalar12996, tp12996, tm12996, ep12996, em12996, dsL]
  · norm_num [world12996, agent12996, scalar12996, tp12996, tm12996, ep12996, em12996, dsL]
  · norm_num [world12996, agent12996, scalar12996, tp12996, tm12996, ep12996, em12996, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12996, agent12996, tp12996, tm12996, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12996, agent12996, tp12996, tm12996, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12996, agent12996, scalar12996, tp12996, tm12996, ep12996, em12996, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12996, agent12996, tp12996, tm12996, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12996, agent12996, scalar12996, tp12996, tm12996, ep12996, em12996, dsL]

theorem tails12996 :
    exp (-((12996:ℝ)*ep12996)) ≤ scalar12996.upperTail ∧
    exp (-((12996:ℝ)*em12996)) ≤ scalar12996.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12996:ℝ)) (by norm_num [ep12996]) ?_)
      (show bp12996^8 ≤ scalar12996.upperTail by norm_num [bp12996, scalar12996])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12996, bp12996, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12996:ℝ)) (by norm_num [em12996]) ?_)
      (show bm12996^8 ≤ scalar12996.lowerTail by norm_num [bm12996, scalar12996])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12996, bm12996, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12996 :
    agent12996.root+dsL+scalar12996.worldRadius < √(1/100/aL) ∧
    2*(agent12996.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12996, agent12996, scalar12996, tp12996, tm12996, ep12996, em12996, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12996, agent12996, scalar12996, tp12996, tm12996, ep12996, em12996, dsL]

noncomputable def master12996 : MasterCertificate 12996 world12996 agent12996 :=
  master scalar12996 dsL tp12996 tm12996 ep12996 em12996
    (by norm_num [dsL]) (by norm_num [tp12996]) (by norm_num [tm12996])
    (by norm_num [ep12996]) (by norm_num [em12996])
    positive12996 negative12996 tails12996.1 tails12996.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12996.1 tailGuards12996.2

theorem preserves12996 : master12996.toScalarCertificate = scalar12996 := rfl

noncomputable def tp12997 : ℝ := (2342475929 / 10000000000)
noncomputable def tm12997 : ℝ := (-((1530071783 / 2500000000)))
noncomputable def ep12997 : ℝ := (52192267290710723 / 100000000000000000000)
noncomputable def em12997 : ℝ := (12693707042971067 / 25000000000000000000)
noncomputable def bp12997 : ℝ := (8566023744034961409 / 20000000000000000000)
noncomputable def bm12997 : ℝ := (5478482201792958777 / 12500000000000000000)

theorem positive12997 :
    Eplus aL (agent12997.root+dsL) scalar12997.worldRadius world12997.frame
      agent12997.frame tp12997 ≤ -ep12997 := by
  apply positive_check (eT := (57837296638966844803 / 50000000000000000000)) (y := (38060084970573853673 / 100000000000000000000)) (u := (73158173335481359283 / 50000000000000000000))
  · norm_num [world12997, agent12997, scalar12997, tp12997, tm12997, ep12997, em12997, dsL]
  · norm_num [world12997, agent12997, scalar12997, tp12997, tm12997, ep12997, em12997, dsL]
  · norm_num [world12997, agent12997, scalar12997, tp12997, tm12997, ep12997, em12997, dsL]
  · norm_num [world12997, agent12997, scalar12997, tp12997, tm12997, ep12997, em12997, dsL]
  · norm_num [world12997, agent12997, scalar12997, tp12997, tm12997, ep12997, em12997, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12997, agent12997, tp12997, tm12997, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12997, agent12997, scalar12997, tp12997, tm12997, ep12997, em12997, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12997, agent12997, tp12997, tm12997, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12997, agent12997, scalar12997, tp12997, tm12997, ep12997, em12997, dsL]

theorem negative12997 :
    Eminus aL (agent12997.root+dsL) scalar12997.worldRadius world12997.frame
      agent12997.frame tm12997 ≤ -em12997 := by
  apply negative_check (lo := (68355807749943184809 / 100000000000000000000)) (hi := (6835580774994318481 / 10000000000000000000))
    (y := (-((71636384613342546671 / 100000000000000000000)))) (u := (24426269189335596371 / 50000000000000000000))
  · norm_num [world12997, agent12997, scalar12997, tp12997, tm12997, ep12997, em12997, dsL]
  · norm_num [world12997, agent12997, scalar12997, tp12997, tm12997, ep12997, em12997, dsL]
  · norm_num [world12997, agent12997, scalar12997, tp12997, tm12997, ep12997, em12997, dsL]
  · norm_num [world12997, agent12997, scalar12997, tp12997, tm12997, ep12997, em12997, dsL]
  · norm_num [world12997, agent12997, scalar12997, tp12997, tm12997, ep12997, em12997, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12997, agent12997, tp12997, tm12997, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12997, agent12997, tp12997, tm12997, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12997, agent12997, scalar12997, tp12997, tm12997, ep12997, em12997, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12997, agent12997, tp12997, tm12997, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12997, agent12997, scalar12997, tp12997, tm12997, ep12997, em12997, dsL]

theorem tails12997 :
    exp (-((12997:ℝ)*ep12997)) ≤ scalar12997.upperTail ∧
    exp (-((12997:ℝ)*em12997)) ≤ scalar12997.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12997:ℝ)) (by norm_num [ep12997]) ?_)
      (show bp12997^8 ≤ scalar12997.upperTail by norm_num [bp12997, scalar12997])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12997, bp12997, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12997:ℝ)) (by norm_num [em12997]) ?_)
      (show bm12997^8 ≤ scalar12997.lowerTail by norm_num [bm12997, scalar12997])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12997, bm12997, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12997 :
    agent12997.root+dsL+scalar12997.worldRadius < √(1/100/aL) ∧
    2*(agent12997.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12997, agent12997, scalar12997, tp12997, tm12997, ep12997, em12997, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12997, agent12997, scalar12997, tp12997, tm12997, ep12997, em12997, dsL]

noncomputable def master12997 : MasterCertificate 12997 world12997 agent12997 :=
  master scalar12997 dsL tp12997 tm12997 ep12997 em12997
    (by norm_num [dsL]) (by norm_num [tp12997]) (by norm_num [tm12997])
    (by norm_num [ep12997]) (by norm_num [em12997])
    positive12997 negative12997 tails12997.1 tails12997.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12997.1 tailGuards12997.2

theorem preserves12997 : master12997.toScalarCertificate = scalar12997 := rfl

noncomputable def tp12998 : ℝ := (2342551647 / 10000000000)
noncomputable def tm12998 : ℝ := (-((6120448053 / 10000000000)))
noncomputable def ep12998 : ℝ := (52194549702072329 / 100000000000000000000)
noncomputable def em12998 : ℝ := (25388384258454099 / 50000000000000000000)
noncomputable def bp12998 : ℝ := (4282573640333999763 / 10000000000000000000)
noncomputable def bm12998 : ℝ := (43823694415827110577 / 100000000000000000000)

theorem positive12998 :
    Eplus aL (agent12998.root+dsL) scalar12998.worldRadius world12998.frame
      agent12998.frame tp12998 ≤ -ep12998 := by
  apply positive_check (eT := (115674779855459409497 / 100000000000000000000)) (y := (38060772365110300437 / 100000000000000000000)) (u := (5852694097799699087 / 4000000000000000000))
  · norm_num [world12998, agent12998, scalar12998, tp12998, tm12998, ep12998, em12998, dsL]
  · norm_num [world12998, agent12998, scalar12998, tp12998, tm12998, ep12998, em12998, dsL]
  · norm_num [world12998, agent12998, scalar12998, tp12998, tm12998, ep12998, em12998, dsL]
  · norm_num [world12998, agent12998, scalar12998, tp12998, tm12998, ep12998, em12998, dsL]
  · norm_num [world12998, agent12998, scalar12998, tp12998, tm12998, ep12998, em12998, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12998, agent12998, tp12998, tm12998, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12998, agent12998, scalar12998, tp12998, tm12998, ep12998, em12998, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12998, agent12998, tp12998, tm12998, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12998, agent12998, scalar12998, tp12998, tm12998, ep12998, em12998, dsL]

theorem negative12998 :
    Eminus aL (agent12998.root+dsL) scalar12998.worldRadius world12998.frame
      agent12998.frame tm12998 ≤ -em12998 := by
  apply negative_check (lo := (68355676516030236057 / 100000000000000000000)) (hi := (34177838258015118029 / 50000000000000000000))
    (y := (-((35818168480791479331 / 50000000000000000000)))) (u := (12213140414442720009 / 25000000000000000000))
  · norm_num [world12998, agent12998, scalar12998, tp12998, tm12998, ep12998, em12998, dsL]
  · norm_num [world12998, agent12998, scalar12998, tp12998, tm12998, ep12998, em12998, dsL]
  · norm_num [world12998, agent12998, scalar12998, tp12998, tm12998, ep12998, em12998, dsL]
  · norm_num [world12998, agent12998, scalar12998, tp12998, tm12998, ep12998, em12998, dsL]
  · norm_num [world12998, agent12998, scalar12998, tp12998, tm12998, ep12998, em12998, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12998, agent12998, tp12998, tm12998, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12998, agent12998, tp12998, tm12998, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12998, agent12998, scalar12998, tp12998, tm12998, ep12998, em12998, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12998, agent12998, tp12998, tm12998, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12998, agent12998, scalar12998, tp12998, tm12998, ep12998, em12998, dsL]

theorem tails12998 :
    exp (-((12998:ℝ)*ep12998)) ≤ scalar12998.upperTail ∧
    exp (-((12998:ℝ)*em12998)) ≤ scalar12998.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12998:ℝ)) (by norm_num [ep12998]) ?_)
      (show bp12998^8 ≤ scalar12998.upperTail by norm_num [bp12998, scalar12998])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12998, bp12998, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12998:ℝ)) (by norm_num [em12998]) ?_)
      (show bm12998^8 ≤ scalar12998.lowerTail by norm_num [bm12998, scalar12998])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12998, bm12998, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12998 :
    agent12998.root+dsL+scalar12998.worldRadius < √(1/100/aL) ∧
    2*(agent12998.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12998, agent12998, scalar12998, tp12998, tm12998, ep12998, em12998, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12998, agent12998, scalar12998, tp12998, tm12998, ep12998, em12998, dsL]

noncomputable def master12998 : MasterCertificate 12998 world12998 agent12998 :=
  master scalar12998 dsL tp12998 tm12998 ep12998 em12998
    (by norm_num [dsL]) (by norm_num [tp12998]) (by norm_num [tm12998])
    (by norm_num [ep12998]) (by norm_num [em12998])
    positive12998 negative12998 tails12998.1 tails12998.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12998.1 tailGuards12998.2

theorem preserves12998 : master12998.toScalarCertificate = scalar12998 := rfl

noncomputable def tp12999 : ℝ := (468525447 / 2000000000)
noncomputable def tm12999 : ℝ := (-((6120608787 / 10000000000)))
noncomputable def ep12999 : ℝ := (52196830903840309 / 100000000000000000000)
noncomputable def em12999 : ℝ := (6347338466404781 / 12500000000000000000)
noncomputable def bp12999 : ℝ := (4282135513218511701 / 10000000000000000000)
noncomputable def bm12999 : ℝ := (43819532205277642873 / 100000000000000000000)

theorem positive12999 :
    Eplus aL (agent12999.root+dsL) scalar12999.worldRadius world12999.frame
      agent12999.frame tp12999 ≤ -ep12999 := by
  apply positive_check (eT := (5783748276562551349 / 5000000000000000000)) (y := (38061457916126946543 / 100000000000000000000)) (u := (73159177764264007123 / 50000000000000000000))
  · norm_num [world12999, agent12999, scalar12999, tp12999, tm12999, ep12999, em12999, dsL]
  · norm_num [world12999, agent12999, scalar12999, tp12999, tm12999, ep12999, em12999, dsL]
  · norm_num [world12999, agent12999, scalar12999, tp12999, tm12999, ep12999, em12999, dsL]
  · norm_num [world12999, agent12999, scalar12999, tp12999, tm12999, ep12999, em12999, dsL]
  · norm_num [world12999, agent12999, scalar12999, tp12999, tm12999, ep12999, em12999, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12999, agent12999, tp12999, tm12999, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12999, agent12999, scalar12999, tp12999, tm12999, ep12999, em12999, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12999, agent12999, tp12999, tm12999, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12999, agent12999, scalar12999, tp12999, tm12999, ep12999, em12999, dsL]

theorem negative12999 :
    Eminus aL (agent12999.root+dsL) scalar12999.worldRadius world12999.frame
      agent12999.frame tm12999 ≤ -em12999 := by
  apply negative_check (lo := (68355546019777449599 / 100000000000000000000)) (hi := (21361108131180453 / 31250000000000000))
    (y := (-((71636288275473634127 / 100000000000000000000)))) (u := (12213146360547061607 / 25000000000000000000))
  · norm_num [world12999, agent12999, scalar12999, tp12999, tm12999, ep12999, em12999, dsL]
  · norm_num [world12999, agent12999, scalar12999, tp12999, tm12999, ep12999, em12999, dsL]
  · norm_num [world12999, agent12999, scalar12999, tp12999, tm12999, ep12999, em12999, dsL]
  · norm_num [world12999, agent12999, scalar12999, tp12999, tm12999, ep12999, em12999, dsL]
  · norm_num [world12999, agent12999, scalar12999, tp12999, tm12999, ep12999, em12999, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12999, agent12999, tp12999, tm12999, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12999, agent12999, tp12999, tm12999, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12999, agent12999, scalar12999, tp12999, tm12999, ep12999, em12999, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12999, agent12999, tp12999, tm12999, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12999, agent12999, scalar12999, tp12999, tm12999, ep12999, em12999, dsL]

theorem tails12999 :
    exp (-((12999:ℝ)*ep12999)) ≤ scalar12999.upperTail ∧
    exp (-((12999:ℝ)*em12999)) ≤ scalar12999.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12999:ℝ)) (by norm_num [ep12999]) ?_)
      (show bp12999^8 ≤ scalar12999.upperTail by norm_num [bp12999, scalar12999])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12999, bp12999, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12999:ℝ)) (by norm_num [em12999]) ?_)
      (show bm12999^8 ≤ scalar12999.lowerTail by norm_num [bm12999, scalar12999])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12999, bm12999, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12999 :
    agent12999.root+dsL+scalar12999.worldRadius < √(1/100/aL) ∧
    2*(agent12999.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12999, agent12999, scalar12999, tp12999, tm12999, ep12999, em12999, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12999, agent12999, scalar12999, tp12999, tm12999, ep12999, em12999, dsL]

noncomputable def master12999 : MasterCertificate 12999 world12999 agent12999 :=
  master scalar12999 dsL tp12999 tm12999 ep12999 em12999
    (by norm_num [dsL]) (by norm_num [tp12999]) (by norm_num [tm12999])
    (by norm_num [ep12999]) (by norm_num [em12999])
    positive12999 negative12999 tails12999.1 tails12999.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12999.1 tailGuards12999.2

theorem preserves12999 : master12999.toScalarCertificate = scalar12999 := rfl

end BstLean.Part268
