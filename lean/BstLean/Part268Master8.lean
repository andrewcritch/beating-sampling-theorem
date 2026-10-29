import BstLean.Part261Checker
import BstLean.Part268Scalar8
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12550 : ℝ := (575549399 / 2500000000)
noncomputable def tm12550 : ℝ := (-((753898819 / 1250000000)))
noncomputable def ep12550 : ℝ := (50996836189543893 / 100000000000000000000)
noncomputable def em12550 : ℝ := (24868449990474013 / 50000000000000000000)
noncomputable def bp12550 : ℝ := (1123307955783909387 / 2500000000000000000)
noncomputable def bm12550 : ℝ := (5728656444638973979 / 12500000000000000000)

theorem positive12550 :
    Eplus aL (agent12550.root+dsL) scalar12550.worldRadius world12550.frame
      agent12550.frame tp12550 ≤ -ep12550 := by
  apply positive_check (eT := (28886990336950007517 / 25000000000000000000)) (y := (37748933519820301451 / 100000000000000000000)) (u := (145861788784070520581 / 100000000000000000000))
  · norm_num [world12550, agent12550, scalar12550, tp12550, tm12550, ep12550, em12550, dsL]
  · norm_num [world12550, agent12550, scalar12550, tp12550, tm12550, ep12550, em12550, dsL]
  · norm_num [world12550, agent12550, scalar12550, tp12550, tm12550, ep12550, em12550, dsL]
  · norm_num [world12550, agent12550, scalar12550, tp12550, tm12550, ep12550, em12550, dsL]
  · norm_num [world12550, agent12550, scalar12550, tp12550, tm12550, ep12550, em12550, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12550, agent12550, tp12550, tm12550, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12550, agent12550, scalar12550, tp12550, tm12550, ep12550, em12550, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12550, agent12550, tp12550, tm12550, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12550, agent12550, scalar12550, tp12550, tm12550, ep12550, em12550, dsL]

theorem negative12550 :
    Eminus aL (agent12550.root+dsL) scalar12550.worldRadius world12550.frame
      agent12550.frame tm12550 ≤ -em12550 := by
  apply negative_check (lo := (13696457809829348313 / 20000000000000000000)) (hi := (34241144524573370783 / 50000000000000000000))
    (y := (-((71700641297824721523 / 100000000000000000000)))) (u := (12205289360119660707 / 25000000000000000000))
  · norm_num [world12550, agent12550, scalar12550, tp12550, tm12550, ep12550, em12550, dsL]
  · norm_num [world12550, agent12550, scalar12550, tp12550, tm12550, ep12550, em12550, dsL]
  · norm_num [world12550, agent12550, scalar12550, tp12550, tm12550, ep12550, em12550, dsL]
  · norm_num [world12550, agent12550, scalar12550, tp12550, tm12550, ep12550, em12550, dsL]
  · norm_num [world12550, agent12550, scalar12550, tp12550, tm12550, ep12550, em12550, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12550, agent12550, tp12550, tm12550, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12550, agent12550, tp12550, tm12550, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12550, agent12550, scalar12550, tp12550, tm12550, ep12550, em12550, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12550, agent12550, tp12550, tm12550, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12550, agent12550, scalar12550, tp12550, tm12550, ep12550, em12550, dsL]

theorem tails12550 :
    exp (-((12550:ℝ)*ep12550)) ≤ scalar12550.upperTail ∧
    exp (-((12550:ℝ)*em12550)) ≤ scalar12550.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12550:ℝ)) (by norm_num [ep12550]) ?_)
      (show bp12550^8 ≤ scalar12550.upperTail by norm_num [bp12550, scalar12550])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12550, bp12550, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12550:ℝ)) (by norm_num [em12550]) ?_)
      (show bm12550^8 ≤ scalar12550.lowerTail by norm_num [bm12550, scalar12550])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12550, bm12550, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12550 :
    agent12550.root+dsL+scalar12550.worldRadius < √(1/100/aL) ∧
    2*(agent12550.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12550, agent12550, scalar12550, tp12550, tm12550, ep12550, em12550, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12550, agent12550, scalar12550, tp12550, tm12550, ep12550, em12550, dsL]

noncomputable def master12550 : MasterCertificate 12550 world12550 agent12550 :=
  master scalar12550 dsL tp12550 tm12550 ep12550 em12550
    (by norm_num [dsL]) (by norm_num [tp12550]) (by norm_num [tm12550])
    (by norm_num [ep12550]) (by norm_num [em12550])
    positive12550 negative12550 tails12550.1 tails12550.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12550.1 tailGuards12550.2

theorem preserves12550 : master12550.toScalarCertificate = scalar12550 := rfl

noncomputable def tp12551 : ℝ := (575571961 / 2500000000)
noncomputable def tm12551 : ℝ := (-((603138533 / 1000000000)))
noncomputable def ep12551 : ℝ := (25499812035106727 / 50000000000000000000)
noncomputable def em12551 : ℝ := (49739303109206669 / 100000000000000000000)
noncomputable def bp12551 : ℝ := (22463744483633522207 / 50000000000000000000)
noncomputable def bm12551 : ℝ := (22912337335752630787 / 50000000000000000000)

theorem positive12551 :
    Eplus aL (agent12551.root+dsL) scalar12551.worldRadius world12551.frame
      agent12551.frame tp12551 ≤ -ep12551 := by
  apply positive_check (eT := (23109647734060293567 / 20000000000000000000)) (y := (117968046763280747 / 312500000000000000)) (u := (36465754033782699837 / 25000000000000000000))
  · norm_num [world12551, agent12551, scalar12551, tp12551, tm12551, ep12551, em12551, dsL]
  · norm_num [world12551, agent12551, scalar12551, tp12551, tm12551, ep12551, em12551, dsL]
  · norm_num [world12551, agent12551, scalar12551, tp12551, tm12551, ep12551, em12551, dsL]
  · norm_num [world12551, agent12551, scalar12551, tp12551, tm12551, ep12551, em12551, dsL]
  · norm_num [world12551, agent12551, scalar12551, tp12551, tm12551, ep12551, em12551, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12551, agent12551, tp12551, tm12551, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12551, agent12551, scalar12551, tp12551, tm12551, ep12551, em12551, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12551, agent12551, tp12551, tm12551, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12551, agent12551, scalar12551, tp12551, tm12551, ep12551, em12551, dsL]

theorem negative12551 :
    Eminus aL (agent12551.root+dsL) scalar12551.worldRadius world12551.frame
      agent12551.frame tm12551 ≤ -em12551 := by
  apply negative_check (lo := (1712050937565824661 / 2500000000000000000)) (hi := (68482037502632986441 / 100000000000000000000))
    (y := (-((2868030705249302127 / 4000000000000000000)))) (u := (9764219152617133 / 20000000000000000))
  · norm_num [world12551, agent12551, scalar12551, tp12551, tm12551, ep12551, em12551, dsL]
  · norm_num [world12551, agent12551, scalar12551, tp12551, tm12551, ep12551, em12551, dsL]
  · norm_num [world12551, agent12551, scalar12551, tp12551, tm12551, ep12551, em12551, dsL]
  · norm_num [world12551, agent12551, scalar12551, tp12551, tm12551, ep12551, em12551, dsL]
  · norm_num [world12551, agent12551, scalar12551, tp12551, tm12551, ep12551, em12551, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12551, agent12551, tp12551, tm12551, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12551, agent12551, tp12551, tm12551, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12551, agent12551, scalar12551, tp12551, tm12551, ep12551, em12551, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12551, agent12551, tp12551, tm12551, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12551, agent12551, scalar12551, tp12551, tm12551, ep12551, em12551, dsL]

theorem tails12551 :
    exp (-((12551:ℝ)*ep12551)) ≤ scalar12551.upperTail ∧
    exp (-((12551:ℝ)*em12551)) ≤ scalar12551.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12551:ℝ)) (by norm_num [ep12551]) ?_)
      (show bp12551^8 ≤ scalar12551.upperTail by norm_num [bp12551, scalar12551])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12551, bp12551, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12551:ℝ)) (by norm_num [em12551]) ?_)
      (show bm12551^8 ≤ scalar12551.lowerTail by norm_num [bm12551, scalar12551])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12551, bm12551, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12551 :
    agent12551.root+dsL+scalar12551.worldRadius < √(1/100/aL) ∧
    2*(agent12551.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12551, agent12551, scalar12551, tp12551, tm12551, ep12551, em12551, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12551, agent12551, scalar12551, tp12551, tm12551, ep12551, em12551, dsL]

noncomputable def master12551 : MasterCertificate 12551 world12551 agent12551 :=
  master scalar12551 dsL tp12551 tm12551 ep12551 em12551
    (by norm_num [dsL]) (by norm_num [tp12551]) (by norm_num [tm12551])
    (by norm_num [ep12551]) (by norm_num [em12551])
    positive12551 negative12551 tails12551.1 tails12551.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12551.1 tailGuards12551.2

theorem preserves12551 : master12551.toScalarCertificate = scalar12551 := rfl

noncomputable def tp12552 : ℝ := (2302378043 / 10000000000)
noncomputable def tm12552 : ℝ := (-((6031579969 / 10000000000)))
noncomputable def ep12552 : ℝ := (510024106531309 / 1000000000000000000)
noncomputable def em12552 : ℝ := (49741705041184529 / 100000000000000000000)
noncomputable def bp12552 : ℝ := (44922660823825983459 / 100000000000000000000)
noncomputable def bm12552 : ℝ := (9164019765546440913 / 20000000000000000000)

theorem positive12552 :
    Eplus aL (agent12552.root+dsL) scalar12552.worldRadius world12552.frame
      agent12552.frame tp12552 ≤ -ep12552 := by
  apply positive_check (eT := (57774257834934648907 / 50000000000000000000)) (y := (147463343331468903 / 390625000000000000)) (u := (36466060686029197917 / 25000000000000000000))
  · norm_num [world12552, agent12552, scalar12552, tp12552, tm12552, ep12552, em12552, dsL]
  · norm_num [world12552, agent12552, scalar12552, tp12552, tm12552, ep12552, em12552, dsL]
  · norm_num [world12552, agent12552, scalar12552, tp12552, tm12552, ep12552, em12552, dsL]
  · norm_num [world12552, agent12552, scalar12552, tp12552, tm12552, ep12552, em12552, dsL]
  · norm_num [world12552, agent12552, scalar12552, tp12552, tm12552, ep12552, em12552, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12552, agent12552, tp12552, tm12552, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12552, agent12552, scalar12552, tp12552, tm12552, ep12552, em12552, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12552, agent12552, tp12552, tm12552, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12552, agent12552, scalar12552, tp12552, tm12552, ep12552, em12552, dsL]

theorem negative12552 :
    Eminus aL (agent12552.root+dsL) scalar12552.worldRadius world12552.frame
      agent12552.frame tm12552 ≤ -em12552 := by
  apply negative_check (lo := (34240893248545554609 / 50000000000000000000)) (hi := (68481786497091109219 / 100000000000000000000))
    (y := (-((71700893224661552177 / 100000000000000000000)))) (u := (48821034447035925727 / 100000000000000000000))
  · norm_num [world12552, agent12552, scalar12552, tp12552, tm12552, ep12552, em12552, dsL]
  · norm_num [world12552, agent12552, scalar12552, tp12552, tm12552, ep12552, em12552, dsL]
  · norm_num [world12552, agent12552, scalar12552, tp12552, tm12552, ep12552, em12552, dsL]
  · norm_num [world12552, agent12552, scalar12552, tp12552, tm12552, ep12552, em12552, dsL]
  · norm_num [world12552, agent12552, scalar12552, tp12552, tm12552, ep12552, em12552, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12552, agent12552, tp12552, tm12552, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12552, agent12552, tp12552, tm12552, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12552, agent12552, scalar12552, tp12552, tm12552, ep12552, em12552, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12552, agent12552, tp12552, tm12552, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12552, agent12552, scalar12552, tp12552, tm12552, ep12552, em12552, dsL]

theorem tails12552 :
    exp (-((12552:ℝ)*ep12552)) ≤ scalar12552.upperTail ∧
    exp (-((12552:ℝ)*em12552)) ≤ scalar12552.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12552:ℝ)) (by norm_num [ep12552]) ?_)
      (show bp12552^8 ≤ scalar12552.upperTail by norm_num [bp12552, scalar12552])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12552, bp12552, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12552:ℝ)) (by norm_num [em12552]) ?_)
      (show bm12552^8 ≤ scalar12552.lowerTail by norm_num [bm12552, scalar12552])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12552, bm12552, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12552 :
    agent12552.root+dsL+scalar12552.worldRadius < √(1/100/aL) ∧
    2*(agent12552.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12552, agent12552, scalar12552, tp12552, tm12552, ep12552, em12552, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12552, agent12552, scalar12552, tp12552, tm12552, ep12552, em12552, dsL]

noncomputable def master12552 : MasterCertificate 12552 world12552 agent12552 :=
  master scalar12552 dsL tp12552 tm12552 ep12552 em12552
    (by norm_num [dsL]) (by norm_num [tp12552]) (by norm_num [tm12552])
    (by norm_num [ep12552]) (by norm_num [em12552])
    positive12552 negative12552 tails12552.1 tails12552.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12552.1 tailGuards12552.2

theorem preserves12552 : master12552.toScalarCertificate = scalar12552 := rfl

noncomputable def tp12553 : ℝ := (575617047 / 2500000000)
noncomputable def tm12553 : ℝ := (-((1507943667 / 2500000000)))
noncomputable def ep12553 : ℝ := (51005195328450043 / 100000000000000000000)
noncomputable def em12553 : ℝ := (24872052597918557 / 50000000000000000000)
noncomputable def bp12553 : ℝ := (1122945855770799637 / 2500000000000000000)
noncomputable def bm12553 : ℝ := (22907762221745935337 / 50000000000000000000)

theorem positive12553 :
    Eplus aL (agent12553.root+dsL) scalar12553.worldRadius world12553.frame
      agent12553.frame tp12553 ≤ -ep12553 := by
  apply positive_check (eT := (115548792310294919073 / 100000000000000000000)) (y := (589866506528289077 / 1562500000000000000)) (u := (9116591798414326977 / 6250000000000000000))
  · norm_num [world12553, agent12553, scalar12553, tp12553, tm12553, ep12553, em12553, dsL]
  · norm_num [world12553, agent12553, scalar12553, tp12553, tm12553, ep12553, em12553, dsL]
  · norm_num [world12553, agent12553, scalar12553, tp12553, tm12553, ep12553, em12553, dsL]
  · norm_num [world12553, agent12553, scalar12553, tp12553, tm12553, ep12553, em12553, dsL]
  · norm_num [world12553, agent12553, scalar12553, tp12553, tm12553, ep12553, em12553, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12553, agent12553, tp12553, tm12553, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12553, agent12553, scalar12553, tp12553, tm12553, ep12553, em12553, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12553, agent12553, tp12553, tm12553, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12553, agent12553, scalar12553, tp12553, tm12553, ep12553, em12553, dsL]

theorem negative12553 :
    Eminus aL (agent12553.root+dsL) scalar12553.worldRadius world12553.frame
      agent12553.frame tm12553 ≤ -em12553 := by
  apply negative_check (lo := (17120383794256161271 / 25000000000000000000)) (hi := (13696307035404929017 / 20000000000000000000))
    (y := (-((8962627522918320883 / 12500000000000000000)))) (u := (48820972464531927199 / 100000000000000000000))
  · norm_num [world12553, agent12553, scalar12553, tp12553, tm12553, ep12553, em12553, dsL]
  · norm_num [world12553, agent12553, scalar12553, tp12553, tm12553, ep12553, em12553, dsL]
  · norm_num [world12553, agent12553, scalar12553, tp12553, tm12553, ep12553, em12553, dsL]
  · norm_num [world12553, agent12553, scalar12553, tp12553, tm12553, ep12553, em12553, dsL]
  · norm_num [world12553, agent12553, scalar12553, tp12553, tm12553, ep12553, em12553, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12553, agent12553, tp12553, tm12553, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12553, agent12553, tp12553, tm12553, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12553, agent12553, scalar12553, tp12553, tm12553, ep12553, em12553, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12553, agent12553, tp12553, tm12553, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12553, agent12553, scalar12553, tp12553, tm12553, ep12553, em12553, dsL]

theorem tails12553 :
    exp (-((12553:ℝ)*ep12553)) ≤ scalar12553.upperTail ∧
    exp (-((12553:ℝ)*em12553)) ≤ scalar12553.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12553:ℝ)) (by norm_num [ep12553]) ?_)
      (show bp12553^8 ≤ scalar12553.upperTail by norm_num [bp12553, scalar12553])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12553, bp12553, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12553:ℝ)) (by norm_num [em12553]) ?_)
      (show bm12553^8 ≤ scalar12553.lowerTail by norm_num [bm12553, scalar12553])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12553, bm12553, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12553 :
    agent12553.root+dsL+scalar12553.worldRadius < √(1/100/aL) ∧
    2*(agent12553.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12553, agent12553, scalar12553, tp12553, tm12553, ep12553, em12553, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12553, agent12553, scalar12553, tp12553, tm12553, ep12553, em12553, dsL]

noncomputable def master12553 : MasterCertificate 12553 world12553 agent12553 :=
  master scalar12553 dsL tp12553 tm12553 ep12553 em12553
    (by norm_num [dsL]) (by norm_num [tp12553]) (by norm_num [tm12553])
    (by norm_num [ep12553]) (by norm_num [em12553])
    positive12553 negative12553 tails12553.1 tails12553.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12553.1 tailGuards12553.2

theorem preserves12553 : master12553.toScalarCertificate = scalar12553 := rfl

noncomputable def tp12554 : ℝ := (287819789 / 1250000000)
noncomputable def tm12554 : ℝ := (-((603196899 / 1000000000)))
noncomputable def ep12554 : ℝ := (6375997380377207 / 12500000000000000000)
noncomputable def em12554 : ℝ := (49746504448366899 / 100000000000000000000)
noncomputable def bp12554 : ℝ := (22456504260441465783 / 50000000000000000000)
noncomputable def bm12554 : ℝ := (22905475444785407597 / 50000000000000000000)

theorem positive12554 :
    Eplus aL (agent12554.root+dsL) scalar12554.worldRadius world12554.frame
      agent12554.frame tp12554 ≤ -ep12554 := by
  apply positive_check (eT := (14443633603865204629 / 12500000000000000000)) (y := (18876148511214338029 / 50000000000000000000)) (u := (145866694931649633017 / 100000000000000000000))
  · norm_num [world12554, agent12554, scalar12554, tp12554, tm12554, ep12554, em12554, dsL]
  · norm_num [world12554, agent12554, scalar12554, tp12554, tm12554, ep12554, em12554, dsL]
  · norm_num [world12554, agent12554, scalar12554, tp12554, tm12554, ep12554, em12554, dsL]
  · norm_num [world12554, agent12554, scalar12554, tp12554, tm12554, ep12554, em12554, dsL]
  · norm_num [world12554, agent12554, scalar12554, tp12554, tm12554, ep12554, em12554, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12554, agent12554, tp12554, tm12554, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12554, agent12554, scalar12554, tp12554, tm12554, ep12554, em12554, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12554, agent12554, tp12554, tm12554, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12554, agent12554, scalar12554, tp12554, tm12554, ep12554, em12554, dsL]

theorem negative12554 :
    Eminus aL (agent12554.root+dsL) scalar12554.worldRadius world12554.frame
      agent12554.frame tm12554 ≤ -em12554 := by
  apply negative_check (lo := (68481285420877413171 / 100000000000000000000)) (hi := (17120321355219353293 / 25000000000000000000))
    (y := (-((71701144490220928027 / 100000000000000000000)))) (u := (48820911776744743467 / 100000000000000000000))
  · norm_num [world12554, agent12554, scalar12554, tp12554, tm12554, ep12554, em12554, dsL]
  · norm_num [world12554, agent12554, scalar12554, tp12554, tm12554, ep12554, em12554, dsL]
  · norm_num [world12554, agent12554, scalar12554, tp12554, tm12554, ep12554, em12554, dsL]
  · norm_num [world12554, agent12554, scalar12554, tp12554, tm12554, ep12554, em12554, dsL]
  · norm_num [world12554, agent12554, scalar12554, tp12554, tm12554, ep12554, em12554, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12554, agent12554, tp12554, tm12554, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12554, agent12554, tp12554, tm12554, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12554, agent12554, scalar12554, tp12554, tm12554, ep12554, em12554, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12554, agent12554, tp12554, tm12554, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12554, agent12554, scalar12554, tp12554, tm12554, ep12554, em12554, dsL]

theorem tails12554 :
    exp (-((12554:ℝ)*ep12554)) ≤ scalar12554.upperTail ∧
    exp (-((12554:ℝ)*em12554)) ≤ scalar12554.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12554:ℝ)) (by norm_num [ep12554]) ?_)
      (show bp12554^8 ≤ scalar12554.upperTail by norm_num [bp12554, scalar12554])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12554, bp12554, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12554:ℝ)) (by norm_num [em12554]) ?_)
      (show bm12554^8 ≤ scalar12554.lowerTail by norm_num [bm12554, scalar12554])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12554, bm12554, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12554 :
    agent12554.root+dsL+scalar12554.worldRadius < √(1/100/aL) ∧
    2*(agent12554.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12554, agent12554, scalar12554, tp12554, tm12554, ep12554, em12554, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12554, agent12554, scalar12554, tp12554, tm12554, ep12554, em12554, dsL]

noncomputable def master12554 : MasterCertificate 12554 world12554 agent12554 :=
  master scalar12554 dsL tp12554 tm12554 ep12554 em12554
    (by norm_num [dsL]) (by norm_num [tp12554]) (by norm_num [tm12554])
    (by norm_num [ep12554]) (by norm_num [em12554])
    positive12554 negative12554 tails12554.1 tails12554.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12554.1 tailGuards12554.2

theorem preserves12554 : master12554.toScalarCertificate = scalar12554 := rfl

noncomputable def tp12555 : ℝ := (2302648353 / 10000000000)
noncomputable def tm12555 : ℝ := (-((1508040833 / 2500000000)))
noncomputable def ep12555 : ℝ := (51010760995783781 / 100000000000000000000)
noncomputable def em12555 : ℝ := (24874451037593573 / 50000000000000000000)
noncomputable def bp12555 : ℝ := (44908184258529669321 / 100000000000000000000)
noncomputable def bm12555 : ℝ := (9161275737226819163 / 20000000000000000000)

theorem positive12555 :
    Eplus aL (agent12555.root+dsL) scalar12555.worldRadius world12555.frame
      agent12555.frame tp12555 ≤ -ep12555 := by
  apply positive_check (eT := (115549344782108462351 / 100000000000000000000)) (y := (37753136560793390897 / 100000000000000000000)) (u := (72933959771827731191 / 50000000000000000000))
  · norm_num [world12555, agent12555, scalar12555, tp12555, tm12555, ep12555, em12555, dsL]
  · norm_num [world12555, agent12555, scalar12555, tp12555, tm12555, ep12555, em12555, dsL]
  · norm_num [world12555, agent12555, scalar12555, tp12555, tm12555, ep12555, em12555, dsL]
  · norm_num [world12555, agent12555, scalar12555, tp12555, tm12555, ep12555, em12555, dsL]
  · norm_num [world12555, agent12555, scalar12555, tp12555, tm12555, ep12555, em12555, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12555, agent12555, tp12555, tm12555, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12555, agent12555, scalar12555, tp12555, tm12555, ep12555, em12555, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12555, agent12555, tp12555, tm12555, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12555, agent12555, scalar12555, tp12555, tm12555, ep12555, em12555, dsL]

theorem negative12555 :
    Eminus aL (agent12555.root+dsL) scalar12555.worldRadius world12555.frame
      agent12555.frame tm12555 ≤ -em12555 := by
  apply negative_check (lo := (6848103552210231139 / 10000000000000000000)) (hi := (68481035522102311391 / 100000000000000000000))
    (y := (-((17925317370648053843 / 25000000000000000000)))) (u := (48820850754367566277 / 100000000000000000000))
  · norm_num [world12555, agent12555, scalar12555, tp12555, tm12555, ep12555, em12555, dsL]
  · norm_num [world12555, agent12555, scalar12555, tp12555, tm12555, ep12555, em12555, dsL]
  · norm_num [world12555, agent12555, scalar12555, tp12555, tm12555, ep12555, em12555, dsL]
  · norm_num [world12555, agent12555, scalar12555, tp12555, tm12555, ep12555, em12555, dsL]
  · norm_num [world12555, agent12555, scalar12555, tp12555, tm12555, ep12555, em12555, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12555, agent12555, tp12555, tm12555, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12555, agent12555, tp12555, tm12555, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12555, agent12555, scalar12555, tp12555, tm12555, ep12555, em12555, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12555, agent12555, tp12555, tm12555, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12555, agent12555, scalar12555, tp12555, tm12555, ep12555, em12555, dsL]

theorem tails12555 :
    exp (-((12555:ℝ)*ep12555)) ≤ scalar12555.upperTail ∧
    exp (-((12555:ℝ)*em12555)) ≤ scalar12555.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12555:ℝ)) (by norm_num [ep12555]) ?_)
      (show bp12555^8 ≤ scalar12555.upperTail by norm_num [bp12555, scalar12555])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12555, bp12555, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12555:ℝ)) (by norm_num [em12555]) ?_)
      (show bm12555^8 ≤ scalar12555.lowerTail by norm_num [bm12555, scalar12555])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12555, bm12555, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12555 :
    agent12555.root+dsL+scalar12555.worldRadius < √(1/100/aL) ∧
    2*(agent12555.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12555, agent12555, scalar12555, tp12555, tm12555, ep12555, em12555, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12555, agent12555, scalar12555, tp12555, tm12555, ep12555, em12555, dsL]

noncomputable def master12555 : MasterCertificate 12555 world12555 agent12555 :=
  master scalar12555 dsL tp12555 tm12555 ep12555 em12555
    (by norm_num [dsL]) (by norm_num [tp12555]) (by norm_num [tm12555])
    (by norm_num [ep12555]) (by norm_num [em12555])
    positive12555 negative12555 tails12555.1 tails12555.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12555.1 tailGuards12555.2

theorem preserves12555 : master12555.toScalarCertificate = scalar12555 := rfl

noncomputable def tp12556 : ℝ := (460547669 / 2000000000)
noncomputable def tm12556 : ℝ := (-((3016178873 / 5000000000)))
noncomputable def ep12556 : ℝ := (10202708274680201 / 20000000000000000000)
noncomputable def em12556 : ℝ := (1243782455375089 / 2500000000000000000)
noncomputable def bp12556 : ℝ := (22451680656084402009 / 50000000000000000000)
noncomputable def bm12556 : ℝ := (45801807733437809333 / 100000000000000000000)

theorem positive12556 :
    Eplus aL (agent12556.root+dsL) scalar12556.worldRadius world12556.frame
      agent12556.frame tp12556 ≤ -ep12556 := by
  apply positive_check (eT := (28887405102606887193 / 25000000000000000000)) (y := (1887698794288621011 / 5000000000000000000)) (u := (14586914385467854961 / 10000000000000000000))
  · norm_num [world12556, agent12556, scalar12556, tp12556, tm12556, ep12556, em12556, dsL]
  · norm_num [world12556, agent12556, scalar12556, tp12556, tm12556, ep12556, em12556, dsL]
  · norm_num [world12556, agent12556, scalar12556, tp12556, tm12556, ep12556, em12556, dsL]
  · norm_num [world12556, agent12556, scalar12556, tp12556, tm12556, ep12556, em12556, dsL]
  · norm_num [world12556, agent12556, scalar12556, tp12556, tm12556, ep12556, em12556, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12556, agent12556, tp12556, tm12556, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12556, agent12556, scalar12556, tp12556, tm12556, ep12556, em12556, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12556, agent12556, tp12556, tm12556, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12556, agent12556, scalar12556, tp12556, tm12556, ep12556, em12556, dsL]

theorem negative12556 :
    Eminus aL (agent12556.root+dsL) scalar12556.worldRadius world12556.frame
      agent12556.frame tm12556 ≤ -em12556 := by
  apply negative_check (lo := (68480785257276252387 / 100000000000000000000)) (hi := (17120196314319063097 / 25000000000000000000))
    (y := (-((448133727327658591 / 625000000000000000)))) (u := (24410394402855400223 / 50000000000000000000))
  · norm_num [world12556, agent12556, scalar12556, tp12556, tm12556, ep12556, em12556, dsL]
  · norm_num [world12556, agent12556, scalar12556, tp12556, tm12556, ep12556, em12556, dsL]
  · norm_num [world12556, agent12556, scalar12556, tp12556, tm12556, ep12556, em12556, dsL]
  · norm_num [world12556, agent12556, scalar12556, tp12556, tm12556, ep12556, em12556, dsL]
  · norm_num [world12556, agent12556, scalar12556, tp12556, tm12556, ep12556, em12556, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12556, agent12556, tp12556, tm12556, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12556, agent12556, tp12556, tm12556, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12556, agent12556, scalar12556, tp12556, tm12556, ep12556, em12556, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12556, agent12556, tp12556, tm12556, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12556, agent12556, scalar12556, tp12556, tm12556, ep12556, em12556, dsL]

theorem tails12556 :
    exp (-((12556:ℝ)*ep12556)) ≤ scalar12556.upperTail ∧
    exp (-((12556:ℝ)*em12556)) ≤ scalar12556.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12556:ℝ)) (by norm_num [ep12556]) ?_)
      (show bp12556^8 ≤ scalar12556.upperTail by norm_num [bp12556, scalar12556])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12556, bp12556, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12556:ℝ)) (by norm_num [em12556]) ?_)
      (show bm12556^8 ≤ scalar12556.lowerTail by norm_num [bm12556, scalar12556])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12556, bm12556, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12556 :
    agent12556.root+dsL+scalar12556.worldRadius < √(1/100/aL) ∧
    2*(agent12556.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12556, agent12556, scalar12556, tp12556, tm12556, ep12556, em12556, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12556, agent12556, scalar12556, tp12556, tm12556, ep12556, em12556, dsL]

noncomputable def master12556 : MasterCertificate 12556 world12556 agent12556 :=
  master scalar12556 dsL tp12556 tm12556 ep12556 em12556
    (by norm_num [dsL]) (by norm_num [tp12556]) (by norm_num [tm12556])
    (by norm_num [ep12556]) (by norm_num [em12556])
    positive12556 negative12556 tails12556.1 tails12556.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12556.1 tailGuards12556.2

theorem preserves12556 : master12556.toScalarCertificate = scalar12556 := rfl

noncomputable def tp12557 : ℝ := (2302828317 / 10000000000)
noncomputable def tm12557 : ℝ := (-((6032551813 / 10000000000)))
noncomputable def ep12557 : ℝ := (25508160301949831 / 50000000000000000000)
noncomputable def em12557 : ℝ := (12438423328610847 / 25000000000000000000)
noncomputable def bp12557 : ℝ := (22449269690051649511 / 50000000000000000000)
noncomputable def bm12557 : ℝ := (5724654713799781717 / 12500000000000000000)

theorem positive12557 :
    Eplus aL (agent12557.root+dsL) scalar12557.worldRadius world12557.frame
      agent12557.frame tp12557 ≤ -ep12557 := by
  apply positive_check (eT := (28887473981555772463 / 25000000000000000000)) (y := (2359675940816550031 / 6250000000000000000)) (u := (145870367945959532851 / 100000000000000000000))
  · norm_num [world12557, agent12557, scalar12557, tp12557, tm12557, ep12557, em12557, dsL]
  · norm_num [world12557, agent12557, scalar12557, tp12557, tm12557, ep12557, em12557, dsL]
  · norm_num [world12557, agent12557, scalar12557, tp12557, tm12557, ep12557, em12557, dsL]
  · norm_num [world12557, agent12557, scalar12557, tp12557, tm12557, ep12557, em12557, dsL]
  · norm_num [world12557, agent12557, scalar12557, tp12557, tm12557, ep12557, em12557, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12557, agent12557, tp12557, tm12557, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12557, agent12557, scalar12557, tp12557, tm12557, ep12557, em12557, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12557, agent12557, tp12557, tm12557, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12557, agent12557, scalar12557, tp12557, tm12557, ep12557, em12557, dsL]

theorem negative12557 :
    Eminus aL (agent12557.root+dsL) scalar12557.worldRadius world12557.frame
      agent12557.frame tm12557 ≤ -em12557 := by
  apply negative_check (lo := (13696107285458669041 / 20000000000000000000)) (hi := (34240268213646672603 / 50000000000000000000))
    (y := (-((4481345012425925151 / 6250000000000000000)))) (u := (12205182088182040129 / 25000000000000000000))
  · norm_num [world12557, agent12557, scalar12557, tp12557, tm12557, ep12557, em12557, dsL]
  · norm_num [world12557, agent12557, scalar12557, tp12557, tm12557, ep12557, em12557, dsL]
  · norm_num [world12557, agent12557, scalar12557, tp12557, tm12557, ep12557, em12557, dsL]
  · norm_num [world12557, agent12557, scalar12557, tp12557, tm12557, ep12557, em12557, dsL]
  · norm_num [world12557, agent12557, scalar12557, tp12557, tm12557, ep12557, em12557, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12557, agent12557, tp12557, tm12557, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12557, agent12557, tp12557, tm12557, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12557, agent12557, scalar12557, tp12557, tm12557, ep12557, em12557, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12557, agent12557, tp12557, tm12557, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12557, agent12557, scalar12557, tp12557, tm12557, ep12557, em12557, dsL]

theorem tails12557 :
    exp (-((12557:ℝ)*ep12557)) ≤ scalar12557.upperTail ∧
    exp (-((12557:ℝ)*em12557)) ≤ scalar12557.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12557:ℝ)) (by norm_num [ep12557]) ?_)
      (show bp12557^8 ≤ scalar12557.upperTail by norm_num [bp12557, scalar12557])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12557, bp12557, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12557:ℝ)) (by norm_num [em12557]) ?_)
      (show bm12557^8 ≤ scalar12557.lowerTail by norm_num [bm12557, scalar12557])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12557, bm12557, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12557 :
    agent12557.root+dsL+scalar12557.worldRadius < √(1/100/aL) ∧
    2*(agent12557.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12557, agent12557, scalar12557, tp12557, tm12557, ep12557, em12557, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12557, agent12557, scalar12557, tp12557, tm12557, ep12557, em12557, dsL]

noncomputable def master12557 : MasterCertificate 12557 world12557 agent12557 :=
  master scalar12557 dsL tp12557 tm12557 ep12557 em12557
    (by norm_num [dsL]) (by norm_num [tp12557]) (by norm_num [tm12557])
    (by norm_num [ep12557]) (by norm_num [em12557])
    positive12557 negative12557 tails12557.1 tails12557.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12557.1 tailGuards12557.2

theorem preserves12557 : master12557.toScalarCertificate = scalar12557 := rfl

noncomputable def tp12558 : ℝ := (2302918297 / 10000000000)
noncomputable def tm12558 : ℝ := (-((3016372901 / 5000000000)))
noncomputable def ep12558 : ℝ := (12754774682040047 / 25000000000000000000)
noncomputable def em12558 : ℝ := (24878043680358307 / 50000000000000000000)
noncomputable def bp12558 : ℝ := (11223429608375381299 / 25000000000000000000)
noncomputable def bm12558 : ℝ := (45792668626200677853 / 100000000000000000000)

theorem positive12558 :
    Eplus aL (agent12558.root+dsL) scalar12558.worldRadius world12558.frame
      agent12558.frame tp12558 ≤ -ep12558 := by
  apply positive_check (eT := (115550171532570187687 / 100000000000000000000)) (y := (7551130992290005413 / 20000000000000000000)) (u := (18233949141069583787 / 12500000000000000000))
  · norm_num [world12558, agent12558, scalar12558, tp12558, tm12558, ep12558, em12558, dsL]
  · norm_num [world12558, agent12558, scalar12558, tp12558, tm12558, ep12558, em12558, dsL]
  · norm_num [world12558, agent12558, scalar12558, tp12558, tm12558, ep12558, em12558, dsL]
  · norm_num [world12558, agent12558, scalar12558, tp12558, tm12558, ep12558, em12558, dsL]
  · norm_num [world12558, agent12558, scalar12558, tp12558, tm12558, ep12558, em12558, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12558, agent12558, tp12558, tm12558, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12558, agent12558, scalar12558, tp12558, tm12558, ep12558, em12558, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12558, agent12558, tp12558, tm12558, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12558, agent12558, scalar12558, tp12558, tm12558, ep12558, em12558, dsL]

theorem negative12558 :
    Eminus aL (agent12558.root+dsL) scalar12558.worldRadius world12558.frame
      agent12558.frame tm12558 ≤ -em12558 := by
  apply negative_check (lo := (34240143937942772073 / 50000000000000000000)) (hi := (68480287875885544147 / 100000000000000000000))
    (y := (-((71701644583538514589 / 100000000000000000000)))) (u := (48820667627237851329 / 100000000000000000000))
  · norm_num [world12558, agent12558, scalar12558, tp12558, tm12558, ep12558, em12558, dsL]
  · norm_num [world12558, agent12558, scalar12558, tp12558, tm12558, ep12558, em12558, dsL]
  · norm_num [world12558, agent12558, scalar12558, tp12558, tm12558, ep12558, em12558, dsL]
  · norm_num [world12558, agent12558, scalar12558, tp12558, tm12558, ep12558, em12558, dsL]
  · norm_num [world12558, agent12558, scalar12558, tp12558, tm12558, ep12558, em12558, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12558, agent12558, tp12558, tm12558, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12558, agent12558, tp12558, tm12558, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12558, agent12558, scalar12558, tp12558, tm12558, ep12558, em12558, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12558, agent12558, tp12558, tm12558, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12558, agent12558, scalar12558, tp12558, tm12558, ep12558, em12558, dsL]

theorem tails12558 :
    exp (-((12558:ℝ)*ep12558)) ≤ scalar12558.upperTail ∧
    exp (-((12558:ℝ)*em12558)) ≤ scalar12558.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12558:ℝ)) (by norm_num [ep12558]) ?_)
      (show bp12558^8 ≤ scalar12558.upperTail by norm_num [bp12558, scalar12558])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12558, bp12558, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12558:ℝ)) (by norm_num [em12558]) ?_)
      (show bm12558^8 ≤ scalar12558.lowerTail by norm_num [bm12558, scalar12558])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12558, bm12558, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12558 :
    agent12558.root+dsL+scalar12558.worldRadius < √(1/100/aL) ∧
    2*(agent12558.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12558, agent12558, scalar12558, tp12558, tm12558, ep12558, em12558, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12558, agent12558, scalar12558, tp12558, tm12558, ep12558, em12558, dsL]

noncomputable def master12558 : MasterCertificate 12558 world12558 agent12558 :=
  master scalar12558 dsL tp12558 tm12558 ep12558 em12558
    (by norm_num [dsL]) (by norm_num [tp12558]) (by norm_num [tm12558])
    (by norm_num [ep12558]) (by norm_num [em12558])
    positive12558 negative12558 tails12558.1 tails12558.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12558.1 tailGuards12558.2

theorem preserves12558 : master12558.toScalarCertificate = scalar12558 := rfl

noncomputable def tp12559 : ℝ := (1151504083 / 5000000000)
noncomputable def tm12559 : ℝ := (-((6032939819 / 10000000000)))
noncomputable def ep12559 : ℝ := (12755468773867147 / 25000000000000000000)
noncomputable def em12559 : ℝ := (49758479785621169 / 100000000000000000000)
noncomputable def bp12559 : ℝ := (22444449465450670889 / 50000000000000000000)
noncomputable def bm12559 : ℝ := (45788100889268606407 / 100000000000000000000)

theorem positive12559 :
    Eplus aL (agent12559.root+dsL) scalar12559.worldRadius world12559.frame
      agent12559.frame tp12559 ≤ -ep12559 := by
  apply positive_check (eT := (451368931118997021 / 390625000000000000)) (y := (9439123327449276917 / 25000000000000000000)) (u := (4558525501430395927 / 3125000000000000000))
  · norm_num [world12559, agent12559, scalar12559, tp12559, tm12559, ep12559, em12559, dsL]
  · norm_num [world12559, agent12559, scalar12559, tp12559, tm12559, ep12559, em12559, dsL]
  · norm_num [world12559, agent12559, scalar12559, tp12559, tm12559, ep12559, em12559, dsL]
  · norm_num [world12559, agent12559, scalar12559, tp12559, tm12559, ep12559, em12559, dsL]
  · norm_num [world12559, agent12559, scalar12559, tp12559, tm12559, ep12559, em12559, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12559, agent12559, tp12559, tm12559, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12559, agent12559, scalar12559, tp12559, tm12559, ep12559, em12559, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12559, agent12559, tp12559, tm12559, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12559, agent12559, scalar12559, tp12559, tm12559, ep12559, em12559, dsL]

theorem negative12559 :
    Eminus aL (agent12559.root+dsL) scalar12559.worldRadius world12559.frame
      agent12559.frame tm12559 ≤ -em12559 := by
  apply negative_check (lo := (34240019573745491223 / 50000000000000000000)) (hi := (68480039147490982447 / 100000000000000000000))
    (y := (-((14340353946046777317 / 20000000000000000000)))) (u := (3051287908113993 / 6250000000000000))
  · norm_num [world12559, agent12559, scalar12559, tp12559, tm12559, ep12559, em12559, dsL]
  · norm_num [world12559, agent12559, scalar12559, tp12559, tm12559, ep12559, em12559, dsL]
  · norm_num [world12559, agent12559, scalar12559, tp12559, tm12559, ep12559, em12559, dsL]
  · norm_num [world12559, agent12559, scalar12559, tp12559, tm12559, ep12559, em12559, dsL]
  · norm_num [world12559, agent12559, scalar12559, tp12559, tm12559, ep12559, em12559, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12559, agent12559, tp12559, tm12559, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12559, agent12559, tp12559, tm12559, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12559, agent12559, scalar12559, tp12559, tm12559, ep12559, em12559, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12559, agent12559, tp12559, tm12559, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12559, agent12559, scalar12559, tp12559, tm12559, ep12559, em12559, dsL]

theorem tails12559 :
    exp (-((12559:ℝ)*ep12559)) ≤ scalar12559.upperTail ∧
    exp (-((12559:ℝ)*em12559)) ≤ scalar12559.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12559:ℝ)) (by norm_num [ep12559]) ?_)
      (show bp12559^8 ≤ scalar12559.upperTail by norm_num [bp12559, scalar12559])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12559, bp12559, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12559:ℝ)) (by norm_num [em12559]) ?_)
      (show bm12559^8 ≤ scalar12559.lowerTail by norm_num [bm12559, scalar12559])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12559, bm12559, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12559 :
    agent12559.root+dsL+scalar12559.worldRadius < √(1/100/aL) ∧
    2*(agent12559.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12559, agent12559, scalar12559, tp12559, tm12559, ep12559, em12559, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12559, agent12559, scalar12559, tp12559, tm12559, ep12559, em12559, dsL]

noncomputable def master12559 : MasterCertificate 12559 world12559 agent12559 :=
  master scalar12559 dsL tp12559 tm12559 ep12559 em12559
    (by norm_num [dsL]) (by norm_num [tp12559]) (by norm_num [tm12559])
    (by norm_num [ep12559]) (by norm_num [em12559])
    positive12559 negative12559 tails12559.1 tails12559.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12559.1 tailGuards12559.2

theorem preserves12559 : master12559.toScalarCertificate = scalar12559 := rfl

noncomputable def tp12560 : ℝ := (230317361 / 1000000000)
noncomputable def tm12560 : ℝ := (-((1206672447 / 2000000000)))
noncomputable def ep12560 : ℝ := (79728284593383 / 156250000000000000)
noncomputable def em12560 : ℝ := (24881225594210233 / 50000000000000000000)
noncomputable def bp12560 : ℝ := (897661147653275367 / 2000000000000000000)
noncomputable def bm12560 : ℝ := (11445599594139170869 / 25000000000000000000)

theorem positive12560 :
    Eplus aL (agent12560.root+dsL) scalar12560.worldRadius world12560.frame
      agent12560.frame tp12560 ≤ -ep12560 := by
  apply positive_check (eT := (28887817322451270621 / 25000000000000000000)) (y := (37756601544484217217 / 100000000000000000000)) (u := (29174594786168827577 / 20000000000000000000))
  · norm_num [world12560, agent12560, scalar12560, tp12560, tm12560, ep12560, em12560, dsL]
  · norm_num [world12560, agent12560, scalar12560, tp12560, tm12560, ep12560, em12560, dsL]
  · norm_num [world12560, agent12560, scalar12560, tp12560, tm12560, ep12560, em12560, dsL]
  · norm_num [world12560, agent12560, scalar12560, tp12560, tm12560, ep12560, em12560, dsL]
  · norm_num [world12560, agent12560, scalar12560, tp12560, tm12560, ep12560, em12560, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12560, agent12560, tp12560, tm12560, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12560, agent12560, scalar12560, tp12560, tm12560, ep12560, em12560, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12560, agent12560, tp12560, tm12560, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12560, agent12560, scalar12560, tp12560, tm12560, ep12560, em12560, dsL]

theorem negative12560 :
    Eminus aL (agent12560.root+dsL) scalar12560.worldRadius world12560.frame
      agent12560.frame tm12560 ≤ -em12560 := by
  apply negative_check (lo := (68478808778814392803 / 100000000000000000000)) (hi := (17119702194703598201 / 25000000000000000000))
    (y := (-((71699970543246668107 / 100000000000000000000)))) (u := (48821484911725496467 / 100000000000000000000))
  · norm_num [world12560, agent12560, scalar12560, tp12560, tm12560, ep12560, em12560, dsL]
  · norm_num [world12560, agent12560, scalar12560, tp12560, tm12560, ep12560, em12560, dsL]
  · norm_num [world12560, agent12560, scalar12560, tp12560, tm12560, ep12560, em12560, dsL]
  · norm_num [world12560, agent12560, scalar12560, tp12560, tm12560, ep12560, em12560, dsL]
  · norm_num [world12560, agent12560, scalar12560, tp12560, tm12560, ep12560, em12560, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12560, agent12560, tp12560, tm12560, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12560, agent12560, tp12560, tm12560, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12560, agent12560, scalar12560, tp12560, tm12560, ep12560, em12560, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12560, agent12560, tp12560, tm12560, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12560, agent12560, scalar12560, tp12560, tm12560, ep12560, em12560, dsL]

theorem tails12560 :
    exp (-((12560:ℝ)*ep12560)) ≤ scalar12560.upperTail ∧
    exp (-((12560:ℝ)*em12560)) ≤ scalar12560.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12560:ℝ)) (by norm_num [ep12560]) ?_)
      (show bp12560^8 ≤ scalar12560.upperTail by norm_num [bp12560, scalar12560])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12560, bp12560, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12560:ℝ)) (by norm_num [em12560]) ?_)
      (show bm12560^8 ≤ scalar12560.lowerTail by norm_num [bm12560, scalar12560])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12560, bm12560, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12560 :
    agent12560.root+dsL+scalar12560.worldRadius < √(1/100/aL) ∧
    2*(agent12560.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12560, agent12560, scalar12560, tp12560, tm12560, ep12560, em12560, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12560, agent12560, scalar12560, tp12560, tm12560, ep12560, em12560, dsL]

noncomputable def master12560 : MasterCertificate 12560 world12560 agent12560 :=
  master scalar12560 dsL tp12560 tm12560 ep12560 em12560
    (by norm_num [dsL]) (by norm_num [tp12560]) (by norm_num [tm12560])
    (by norm_num [ep12560]) (by norm_num [em12560])
    positive12560 negative12560 tails12560.1 tails12560.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12560.1 tailGuards12560.2

theorem preserves12560 : master12560.toScalarCertificate = scalar12560 := rfl

noncomputable def tp12561 : ℝ := (1151631703 / 5000000000)
noncomputable def tm12561 : ℝ := (-((1206711167 / 2000000000)))
noncomputable def ep12561 : ℝ := (51028875423811887 / 100000000000000000000)
noncomputable def em12561 : ℝ := (49764840757539291 / 100000000000000000000)
noncomputable def bp12561 : ℝ := (22439120246398452207 / 50000000000000000000)
noncomputable def bm12561 : ℝ := (45777833078761610873 / 100000000000000000000)

theorem positive12561 :
    Eplus aL (agent12561.root+dsL) scalar12561.worldRadius world12561.frame
      agent12561.frame tp12561 ≤ -ep12561 := by
  apply positive_check (eT := (23110308729664754493 / 20000000000000000000)) (y := (37757439409506114899 / 100000000000000000000)) (u := (36468549038647347957 / 25000000000000000000))
  · norm_num [world12561, agent12561, scalar12561, tp12561, tm12561, ep12561, em12561, dsL]
  · norm_num [world12561, agent12561, scalar12561, tp12561, tm12561, ep12561, em12561, dsL]
  · norm_num [world12561, agent12561, scalar12561, tp12561, tm12561, ep12561, em12561, dsL]
  · norm_num [world12561, agent12561, scalar12561, tp12561, tm12561, ep12561, em12561, dsL]
  · norm_num [world12561, agent12561, scalar12561, tp12561, tm12561, ep12561, em12561, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12561, agent12561, tp12561, tm12561, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12561, agent12561, scalar12561, tp12561, tm12561, ep12561, em12561, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12561, agent12561, tp12561, tm12561, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12561, agent12561, scalar12561, tp12561, tm12561, ep12561, em12561, dsL]

theorem negative12561 :
    Eminus aL (agent12561.root+dsL) scalar12561.worldRadius world12561.frame
      agent12561.frame tm12561 ≤ -em12561 := by
  apply negative_check (lo := (6847856175497406179 / 10000000000000000000)) (hi := (68478561754974061791 / 100000000000000000000))
    (y := (-((35850046441447476789 / 50000000000000000000)))) (u := (12205356295932275809 / 25000000000000000000))
  · norm_num [world12561, agent12561, scalar12561, tp12561, tm12561, ep12561, em12561, dsL]
  · norm_num [world12561, agent12561, scalar12561, tp12561, tm12561, ep12561, em12561, dsL]
  · norm_num [world12561, agent12561, scalar12561, tp12561, tm12561, ep12561, em12561, dsL]
  · norm_num [world12561, agent12561, scalar12561, tp12561, tm12561, ep12561, em12561, dsL]
  · norm_num [world12561, agent12561, scalar12561, tp12561, tm12561, ep12561, em12561, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12561, agent12561, tp12561, tm12561, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12561, agent12561, tp12561, tm12561, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12561, agent12561, scalar12561, tp12561, tm12561, ep12561, em12561, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12561, agent12561, tp12561, tm12561, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12561, agent12561, scalar12561, tp12561, tm12561, ep12561, em12561, dsL]

theorem tails12561 :
    exp (-((12561:ℝ)*ep12561)) ≤ scalar12561.upperTail ∧
    exp (-((12561:ℝ)*em12561)) ≤ scalar12561.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12561:ℝ)) (by norm_num [ep12561]) ?_)
      (show bp12561^8 ≤ scalar12561.upperTail by norm_num [bp12561, scalar12561])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12561, bp12561, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12561:ℝ)) (by norm_num [em12561]) ?_)
      (show bm12561^8 ≤ scalar12561.lowerTail by norm_num [bm12561, scalar12561])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12561, bm12561, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12561 :
    agent12561.root+dsL+scalar12561.worldRadius < √(1/100/aL) ∧
    2*(agent12561.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12561, agent12561, scalar12561, tp12561, tm12561, ep12561, em12561, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12561, agent12561, scalar12561, tp12561, tm12561, ep12561, em12561, dsL]

noncomputable def master12561 : MasterCertificate 12561 world12561 agent12561 :=
  master scalar12561 dsL tp12561 tm12561 ep12561 em12561
    (by norm_num [dsL]) (by norm_num [tp12561]) (by norm_num [tm12561])
    (by norm_num [ep12561]) (by norm_num [em12561])
    positive12561 negative12561 tails12561.1 tails12561.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12561.1 tailGuards12561.2

theorem preserves12561 : master12561.toScalarCertificate = scalar12561 := rfl

noncomputable def tp12562 : ℝ := (575838281 / 2500000000)
noncomputable def tm12562 : ℝ := (-((377109343 / 625000000)))
noncomputable def ep12562 : ℝ := (51031647930854413 / 100000000000000000000)
noncomputable def em12562 : ℝ := (49767229554590589 / 100000000000000000000)
noncomputable def bp12562 : ℝ := (22436712178131330369 / 50000000000000000000)
noncomputable def bm12562 : ℝ := (11443317129421750099 / 25000000000000000000)

theorem positive12562 :
    Eplus aL (agent12562.root+dsL) scalar12562.worldRadius world12562.frame
      agent12562.frame tp12562 ≤ -ep12562 := by
  apply positive_check (eT := (28887954368439882959 / 25000000000000000000)) (y := (37758276501656404261 / 100000000000000000000)) (u := (36468854315286396509 / 25000000000000000000))
  · norm_num [world12562, agent12562, scalar12562, tp12562, tm12562, ep12562, em12562, dsL]
  · norm_num [world12562, agent12562, scalar12562, tp12562, tm12562, ep12562, em12562, dsL]
  · norm_num [world12562, agent12562, scalar12562, tp12562, tm12562, ep12562, em12562, dsL]
  · norm_num [world12562, agent12562, scalar12562, tp12562, tm12562, ep12562, em12562, dsL]
  · norm_num [world12562, agent12562, scalar12562, tp12562, tm12562, ep12562, em12562, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12562, agent12562, tp12562, tm12562, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12562, agent12562, scalar12562, tp12562, tm12562, ep12562, em12562, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12562, agent12562, tp12562, tm12562, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12562, agent12562, scalar12562, tp12562, tm12562, ep12562, em12562, dsL]

theorem negative12562 :
    Eminus aL (agent12562.root+dsL) scalar12562.worldRadius world12562.frame
      agent12562.frame tm12562 ≤ -em12562 := by
  apply negative_check (lo := (68478314446689265363 / 100000000000000000000)) (hi := (17119578611672316341 / 25000000000000000000))
    (y := (-((71700217063265875457 / 100000000000000000000)))) (u := (48821364557139863903 / 100000000000000000000))
  · norm_num [world12562, agent12562, scalar12562, tp12562, tm12562, ep12562, em12562, dsL]
  · norm_num [world12562, agent12562, scalar12562, tp12562, tm12562, ep12562, em12562, dsL]
  · norm_num [world12562, agent12562, scalar12562, tp12562, tm12562, ep12562, em12562, dsL]
  · norm_num [world12562, agent12562, scalar12562, tp12562, tm12562, ep12562, em12562, dsL]
  · norm_num [world12562, agent12562, scalar12562, tp12562, tm12562, ep12562, em12562, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12562, agent12562, tp12562, tm12562, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12562, agent12562, tp12562, tm12562, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12562, agent12562, scalar12562, tp12562, tm12562, ep12562, em12562, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12562, agent12562, tp12562, tm12562, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12562, agent12562, scalar12562, tp12562, tm12562, ep12562, em12562, dsL]

theorem tails12562 :
    exp (-((12562:ℝ)*ep12562)) ≤ scalar12562.upperTail ∧
    exp (-((12562:ℝ)*em12562)) ≤ scalar12562.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12562:ℝ)) (by norm_num [ep12562]) ?_)
      (show bp12562^8 ≤ scalar12562.upperTail by norm_num [bp12562, scalar12562])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12562, bp12562, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12562:ℝ)) (by norm_num [em12562]) ?_)
      (show bm12562^8 ≤ scalar12562.lowerTail by norm_num [bm12562, scalar12562])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12562, bm12562, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12562 :
    agent12562.root+dsL+scalar12562.worldRadius < √(1/100/aL) ∧
    2*(agent12562.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12562, agent12562, scalar12562, tp12562, tm12562, ep12562, em12562, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12562, agent12562, scalar12562, tp12562, tm12562, ep12562, em12562, dsL]

noncomputable def master12562 : MasterCertificate 12562 world12562 agent12562 :=
  master scalar12562 dsL tp12562 tm12562 ep12562 em12562
    (by norm_num [dsL]) (by norm_num [tp12562]) (by norm_num [tm12562])
    (by norm_num [ep12562]) (by norm_num [em12562])
    positive12562 negative12562 tails12562.1 tails12562.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12562.1 tailGuards12562.2

theorem preserves12562 : master12562.toScalarCertificate = scalar12562 := rfl

noncomputable def tp12563 : ℝ := (575860717 / 2500000000)
noncomputable def tm12563 : ℝ := (-((1206788617 / 2000000000)))
noncomputable def ep12563 : ℝ := (25517209415122749 / 50000000000000000000)
noncomputable def em12563 : ℝ := (12442404222880361 / 25000000000000000000)
noncomputable def bp12563 : ℝ := (44868609558338713909 / 100000000000000000000)
noncomputable def bm12563 : ℝ := (9153741037573425549 / 20000000000000000000)

theorem positive12563 :
    Eplus aL (agent12563.root+dsL) scalar12563.worldRadius world12563.frame
      agent12563.frame tp12563 ≤ -ep12563 := by
  apply positive_check (eT := (115552091520300225219 / 100000000000000000000)) (y := (18879557197714407879 / 50000000000000000000)) (u := (145876639547303019107 / 100000000000000000000))
  · norm_num [world12563, agent12563, scalar12563, tp12563, tm12563, ep12563, em12563, dsL]
  · norm_num [world12563, agent12563, scalar12563, tp12563, tm12563, ep12563, em12563, dsL]
  · norm_num [world12563, agent12563, scalar12563, tp12563, tm12563, ep12563, em12563, dsL]
  · norm_num [world12563, agent12563, scalar12563, tp12563, tm12563, ep12563, em12563, dsL]
  · norm_num [world12563, agent12563, scalar12563, tp12563, tm12563, ep12563, em12563, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12563, agent12563, tp12563, tm12563, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12563, agent12563, scalar12563, tp12563, tm12563, ep12563, em12563, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12563, agent12563, tp12563, tm12563, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12563, agent12563, scalar12563, tp12563, tm12563, ep12563, em12563, dsL]

theorem negative12563 :
    Eminus aL (agent12563.root+dsL) scalar12563.worldRadius world12563.frame
      agent12563.frame tm12563 ≤ -em12563 := by
  apply negative_check (lo := (17119516830593823767 / 25000000000000000000)) (hi := (68478067322375295069 / 100000000000000000000))
    (y := (-((7170034130774488091 / 10000000000000000000)))) (u := (48821303899327508531 / 100000000000000000000))
  · norm_num [world12563, agent12563, scalar12563, tp12563, tm12563, ep12563, em12563, dsL]
  · norm_num [world12563, agent12563, scalar12563, tp12563, tm12563, ep12563, em12563, dsL]
  · norm_num [world12563, agent12563, scalar12563, tp12563, tm12563, ep12563, em12563, dsL]
  · norm_num [world12563, agent12563, scalar12563, tp12563, tm12563, ep12563, em12563, dsL]
  · norm_num [world12563, agent12563, scalar12563, tp12563, tm12563, ep12563, em12563, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12563, agent12563, tp12563, tm12563, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12563, agent12563, tp12563, tm12563, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12563, agent12563, scalar12563, tp12563, tm12563, ep12563, em12563, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12563, agent12563, tp12563, tm12563, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12563, agent12563, scalar12563, tp12563, tm12563, ep12563, em12563, dsL]

theorem tails12563 :
    exp (-((12563:ℝ)*ep12563)) ≤ scalar12563.upperTail ∧
    exp (-((12563:ℝ)*em12563)) ≤ scalar12563.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12563:ℝ)) (by norm_num [ep12563]) ?_)
      (show bp12563^8 ≤ scalar12563.upperTail by norm_num [bp12563, scalar12563])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12563, bp12563, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12563:ℝ)) (by norm_num [em12563]) ?_)
      (show bm12563^8 ≤ scalar12563.lowerTail by norm_num [bm12563, scalar12563])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12563, bm12563, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12563 :
    agent12563.root+dsL+scalar12563.worldRadius < √(1/100/aL) ∧
    2*(agent12563.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12563, agent12563, scalar12563, tp12563, tm12563, ep12563, em12563, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12563, agent12563, scalar12563, tp12563, tm12563, ep12563, em12563, dsL]

noncomputable def master12563 : MasterCertificate 12563 world12563 agent12563 :=
  master scalar12563 dsL tp12563 tm12563 ep12563 em12563
    (by norm_num [dsL]) (by norm_num [tp12563]) (by norm_num [tm12563])
    (by norm_num [ep12563]) (by norm_num [em12563])
    positive12563 negative12563 tails12563.1 tails12563.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12563.1 tailGuards12563.2

theorem preserves12563 : master12563.toScalarCertificate = scalar12563 := rfl

noncomputable def tp12564 : ℝ := (115176627 / 500000000)
noncomputable def tm12564 : ℝ := (-((3017068191 / 5000000000)))
noncomputable def ep12564 : ℝ := (25518594223197897 / 50000000000000000000)
noncomputable def em12564 : ℝ := (24886001522579873 / 50000000000000000000)
noncomputable def bp12564 : ℝ := (4486379587040037279 / 10000000000000000000)
noncomputable def bm12564 : ℝ := (1144103572257792549 / 2500000000000000000)

theorem positive12564 :
    Eplus aL (agent12564.root+dsL) scalar12564.worldRadius world12564.frame
      agent12564.frame tp12564 ≤ -ep12564 := by
  apply positive_check (eT := (115552365077291763787 / 100000000000000000000)) (y := (18879975683123485999 / 50000000000000000000)) (u := (145877860497316027527 / 100000000000000000000))
  · norm_num [world12564, agent12564, scalar12564, tp12564, tm12564, ep12564, em12564, dsL]
  · norm_num [world12564, agent12564, scalar12564, tp12564, tm12564, ep12564, em12564, dsL]
  · norm_num [world12564, agent12564, scalar12564, tp12564, tm12564, ep12564, em12564, dsL]
  · norm_num [world12564, agent12564, scalar12564, tp12564, tm12564, ep12564, em12564, dsL]
  · norm_num [world12564, agent12564, scalar12564, tp12564, tm12564, ep12564, em12564, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12564, agent12564, tp12564, tm12564, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12564, agent12564, scalar12564, tp12564, tm12564, ep12564, em12564, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12564, agent12564, tp12564, tm12564, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12564, agent12564, scalar12564, tp12564, tm12564, ep12564, em12564, dsL]

theorem negative12564 :
    Eminus aL (agent12564.root+dsL) scalar12564.worldRadius world12564.frame
      agent12564.frame tm12564 ≤ -em12564 := by
  apply negative_check (lo := (68477821430560386711 / 100000000000000000000)) (hi := (8559727678820048339 / 12500000000000000000))
    (y := (-((71700463234353673483 / 100000000000000000000)))) (u := (1525663886662612027 / 3125000000000000000))
  · norm_num [world12564, agent12564, scalar12564, tp12564, tm12564, ep12564, em12564, dsL]
  · norm_num [world12564, agent12564, scalar12564, tp12564, tm12564, ep12564, em12564, dsL]
  · norm_num [world12564, agent12564, scalar12564, tp12564, tm12564, ep12564, em12564, dsL]
  · norm_num [world12564, agent12564, scalar12564, tp12564, tm12564, ep12564, em12564, dsL]
  · norm_num [world12564, agent12564, scalar12564, tp12564, tm12564, ep12564, em12564, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12564, agent12564, tp12564, tm12564, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12564, agent12564, tp12564, tm12564, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12564, agent12564, scalar12564, tp12564, tm12564, ep12564, em12564, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12564, agent12564, tp12564, tm12564, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12564, agent12564, scalar12564, tp12564, tm12564, ep12564, em12564, dsL]

theorem tails12564 :
    exp (-((12564:ℝ)*ep12564)) ≤ scalar12564.upperTail ∧
    exp (-((12564:ℝ)*em12564)) ≤ scalar12564.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12564:ℝ)) (by norm_num [ep12564]) ?_)
      (show bp12564^8 ≤ scalar12564.upperTail by norm_num [bp12564, scalar12564])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12564, bp12564, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12564:ℝ)) (by norm_num [em12564]) ?_)
      (show bm12564^8 ≤ scalar12564.lowerTail by norm_num [bm12564, scalar12564])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12564, bm12564, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12564 :
    agent12564.root+dsL+scalar12564.worldRadius < √(1/100/aL) ∧
    2*(agent12564.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12564, agent12564, scalar12564, tp12564, tm12564, ep12564, em12564, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12564, agent12564, scalar12564, tp12564, tm12564, ep12564, em12564, dsL]

noncomputable def master12564 : MasterCertificate 12564 world12564 agent12564 :=
  master scalar12564 dsL tp12564 tm12564 ep12564 em12564
    (by norm_num [dsL]) (by norm_num [tp12564]) (by norm_num [tm12564])
    (by norm_num [ep12564]) (by norm_num [em12564])
    positive12564 negative12564 tails12564.1 tails12564.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12564.1 tailGuards12564.2

theorem preserves12564 : master12564.toScalarCertificate = scalar12564 := rfl

noncomputable def tp12565 : ℝ := (1151811091 / 5000000000)
noncomputable def tm12565 : ℝ := (-((6034329583 / 10000000000)))
noncomputable def ep12565 : ℝ := (51039956164618809 / 100000000000000000000)
noncomputable def em12565 : ℝ := (49774387430300397 / 100000000000000000000)
noncomputable def bp12565 : ℝ := (44858983725504551349 / 100000000000000000000)
noncomputable def bm12565 : ℝ := (45759582045599367067 / 100000000000000000000)

theorem positive12565 :
    Eplus aL (agent12565.root+dsL) scalar12565.worldRadius world12565.frame
      agent12565.frame tp12565 ≤ -ep12565 := by
  apply positive_check (eT := (7222039903080830051 / 6250000000000000000)) (y := (18880394176859482017 / 50000000000000000000)) (u := (72939540740921268357 / 50000000000000000000))
  · norm_num [world12565, agent12565, scalar12565, tp12565, tm12565, ep12565, em12565, dsL]
  · norm_num [world12565, agent12565, scalar12565, tp12565, tm12565, ep12565, em12565, dsL]
  · norm_num [world12565, agent12565, scalar12565, tp12565, tm12565, ep12565, em12565, dsL]
  · norm_num [world12565, agent12565, scalar12565, tp12565, tm12565, ep12565, em12565, dsL]
  · norm_num [world12565, agent12565, scalar12565, tp12565, tm12565, ep12565, em12565, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12565, agent12565, tp12565, tm12565, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12565, agent12565, scalar12565, tp12565, tm12565, ep12565, em12565, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12565, agent12565, tp12565, tm12565, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12565, agent12565, scalar12565, tp12565, tm12565, ep12565, em12565, dsL]

theorem negative12565 :
    Eminus aL (agent12565.root+dsL) scalar12565.worldRadius world12565.frame
      agent12565.frame tm12565 ≤ -em12565 := by
  apply negative_check (lo := (34238787947286195399 / 50000000000000000000)) (hi := (68477575894572390799 / 100000000000000000000))
    (y := (-((71700584996307413997 / 100000000000000000000)))) (u := (48821184927538786729 / 100000000000000000000))
  · norm_num [world12565, agent12565, scalar12565, tp12565, tm12565, ep12565, em12565, dsL]
  · norm_num [world12565, agent12565, scalar12565, tp12565, tm12565, ep12565, em12565, dsL]
  · norm_num [world12565, agent12565, scalar12565, tp12565, tm12565, ep12565, em12565, dsL]
  · norm_num [world12565, agent12565, scalar12565, tp12565, tm12565, ep12565, em12565, dsL]
  · norm_num [world12565, agent12565, scalar12565, tp12565, tm12565, ep12565, em12565, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12565, agent12565, tp12565, tm12565, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12565, agent12565, tp12565, tm12565, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12565, agent12565, scalar12565, tp12565, tm12565, ep12565, em12565, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12565, agent12565, tp12565, tm12565, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12565, agent12565, scalar12565, tp12565, tm12565, ep12565, em12565, dsL]

theorem tails12565 :
    exp (-((12565:ℝ)*ep12565)) ≤ scalar12565.upperTail ∧
    exp (-((12565:ℝ)*em12565)) ≤ scalar12565.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12565:ℝ)) (by norm_num [ep12565]) ?_)
      (show bp12565^8 ≤ scalar12565.upperTail by norm_num [bp12565, scalar12565])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12565, bp12565, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12565:ℝ)) (by norm_num [em12565]) ?_)
      (show bm12565^8 ≤ scalar12565.lowerTail by norm_num [bm12565, scalar12565])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12565, bm12565, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12565 :
    agent12565.root+dsL+scalar12565.worldRadius < √(1/100/aL) ∧
    2*(agent12565.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12565, agent12565, scalar12565, tp12565, tm12565, ep12565, em12565, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12565, agent12565, scalar12565, tp12565, tm12565, ep12565, em12565, dsL]

noncomputable def master12565 : MasterCertificate 12565 world12565 agent12565 :=
  master scalar12565 dsL tp12565 tm12565 ep12565 em12565
    (by norm_num [dsL]) (by norm_num [tp12565]) (by norm_num [tm12565])
    (by norm_num [ep12565]) (by norm_num [em12565])
    positive12565 negative12565 tails12565.1 tails12565.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12565.1 tailGuards12565.2

theorem preserves12565 : master12565.toScalarCertificate = scalar12565 := rfl

noncomputable def tp12566 : ℝ := (1151855891 / 5000000000)
noncomputable def tm12566 : ℝ := (-((1508630741 / 2500000000)))
noncomputable def ep12566 : ℝ := (5104272292292727 / 10000000000000000000)
noncomputable def em12566 : ℝ := (24888385457335017 / 50000000000000000000)
noncomputable def bp12566 : ℝ := (11213543115677689661 / 25000000000000000000)
noncomputable def bm12566 : ℝ := (22877511015028643863 / 50000000000000000000)

theorem positive12566 :
    Eplus aL (agent12566.root+dsL) scalar12566.worldRadius world12566.frame
      agent12566.frame tp12566 ≤ -ep12566 := by
  apply positive_check (eT := (115552911549313719499 / 100000000000000000000)) (y := (18880812524375589521 / 50000000000000000000)) (u := (5835212081999061821 / 4000000000000000000))
  · norm_num [world12566, agent12566, scalar12566, tp12566, tm12566, ep12566, em12566, dsL]
  · norm_num [world12566, agent12566, scalar12566, tp12566, tm12566, ep12566, em12566, dsL]
  · norm_num [world12566, agent12566, scalar12566, tp12566, tm12566, ep12566, em12566, dsL]
  · norm_num [world12566, agent12566, scalar12566, tp12566, tm12566, ep12566, em12566, dsL]
  · norm_num [world12566, agent12566, scalar12566, tp12566, tm12566, ep12566, em12566, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12566, agent12566, tp12566, tm12566, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12566, agent12566, scalar12566, tp12566, tm12566, ep12566, em12566, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12566, agent12566, tp12566, tm12566, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12566, agent12566, scalar12566, tp12566, tm12566, ep12566, em12566, dsL]

theorem negative12566 :
    Eminus aL (agent12566.root+dsL) scalar12566.worldRadius world12566.frame
      agent12566.frame tm12566 ≤ -em12566 := by
  apply negative_check (lo := (3423866476420400819 / 5000000000000000000)) (hi := (68477329528408016381 / 100000000000000000000))
    (y := (-((71700709547266179117 / 100000000000000000000)))) (u := (48821124120322746981 / 100000000000000000000))
  · norm_num [world12566, agent12566, scalar12566, tp12566, tm12566, ep12566, em12566, dsL]
  · norm_num [world12566, agent12566, scalar12566, tp12566, tm12566, ep12566, em12566, dsL]
  · norm_num [world12566, agent12566, scalar12566, tp12566, tm12566, ep12566, em12566, dsL]
  · norm_num [world12566, agent12566, scalar12566, tp12566, tm12566, ep12566, em12566, dsL]
  · norm_num [world12566, agent12566, scalar12566, tp12566, tm12566, ep12566, em12566, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12566, agent12566, tp12566, tm12566, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12566, agent12566, tp12566, tm12566, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12566, agent12566, scalar12566, tp12566, tm12566, ep12566, em12566, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12566, agent12566, tp12566, tm12566, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12566, agent12566, scalar12566, tp12566, tm12566, ep12566, em12566, dsL]

theorem tails12566 :
    exp (-((12566:ℝ)*ep12566)) ≤ scalar12566.upperTail ∧
    exp (-((12566:ℝ)*em12566)) ≤ scalar12566.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12566:ℝ)) (by norm_num [ep12566]) ?_)
      (show bp12566^8 ≤ scalar12566.upperTail by norm_num [bp12566, scalar12566])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12566, bp12566, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12566:ℝ)) (by norm_num [em12566]) ?_)
      (show bm12566^8 ≤ scalar12566.lowerTail by norm_num [bm12566, scalar12566])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12566, bm12566, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12566 :
    agent12566.root+dsL+scalar12566.worldRadius < √(1/100/aL) ∧
    2*(agent12566.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12566, agent12566, scalar12566, tp12566, tm12566, ep12566, em12566, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12566, agent12566, scalar12566, tp12566, tm12566, ep12566, em12566, dsL]

noncomputable def master12566 : MasterCertificate 12566 world12566 agent12566 :=
  master scalar12566 dsL tp12566 tm12566 ep12566 em12566
    (by norm_num [dsL]) (by norm_num [tp12566]) (by norm_num [tm12566])
    (by norm_num [ep12566]) (by norm_num [em12566])
    positive12566 negative12566 tails12566.1 tails12566.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12566.1 tailGuards12566.2

theorem preserves12566 : master12566.toScalarCertificate = scalar12566 := rfl

noncomputable def tp12567 : ℝ := (2303801289 / 10000000000)
noncomputable def tm12567 : ℝ := (-((6034716007 / 10000000000)))
noncomputable def ep12567 : ℝ := (51045487792610181 / 100000000000000000000)
noncomputable def em12567 : ℝ := (49779152638569043 / 100000000000000000000)
noncomputable def bp12567 : ℝ := (44849362736309691667 / 100000000000000000000)
noncomputable def bm12567 : ℝ := (5718807932691731157 / 12500000000000000000)

theorem positive12567 :
    Eplus aL (agent12567.root+dsL) scalar12567.worldRadius world12567.frame
      agent12567.frame tp12567 ≤ -ep12567 := by
  apply positive_check (eT := (115553184007560418657 / 100000000000000000000)) (y := (18881230325504585877 / 50000000000000000000)) (u := (9117595064635460271 / 6250000000000000000))
  · norm_num [world12567, agent12567, scalar12567, tp12567, tm12567, ep12567, em12567, dsL]
  · norm_num [world12567, agent12567, scalar12567, tp12567, tm12567, ep12567, em12567, dsL]
  · norm_num [world12567, agent12567, scalar12567, tp12567, tm12567, ep12567, em12567, dsL]
  · norm_num [world12567, agent12567, scalar12567, tp12567, tm12567, ep12567, em12567, dsL]
  · norm_num [world12567, agent12567, scalar12567, tp12567, tm12567, ep12567, em12567, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12567, agent12567, tp12567, tm12567, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12567, agent12567, scalar12567, tp12567, tm12567, ep12567, em12567, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12567, agent12567, tp12567, tm12567, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12567, agent12567, scalar12567, tp12567, tm12567, ep12567, em12567, dsL]

theorem negative12567 :
    Eminus aL (agent12567.root+dsL) scalar12567.worldRadius world12567.frame
      agent12567.frame tm12567 ≤ -em12567 := by
  apply negative_check (lo := (13695416911586117721 / 20000000000000000000)) (hi := (34238542278965294303 / 50000000000000000000))
    (y := (-((2868033262703624073 / 4000000000000000000)))) (u := (24410532274332526661 / 50000000000000000000))
  · norm_num [world12567, agent12567, scalar12567, tp12567, tm12567, ep12567, em12567, dsL]
  · norm_num [world12567, agent12567, scalar12567, tp12567, tm12567, ep12567, em12567, dsL]
  · norm_num [world12567, agent12567, scalar12567, tp12567, tm12567, ep12567, em12567, dsL]
  · norm_num [world12567, agent12567, scalar12567, tp12567, tm12567, ep12567, em12567, dsL]
  · norm_num [world12567, agent12567, scalar12567, tp12567, tm12567, ep12567, em12567, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12567, agent12567, tp12567, tm12567, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12567, agent12567, tp12567, tm12567, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12567, agent12567, scalar12567, tp12567, tm12567, ep12567, em12567, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12567, agent12567, tp12567, tm12567, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12567, agent12567, scalar12567, tp12567, tm12567, ep12567, em12567, dsL]

theorem tails12567 :
    exp (-((12567:ℝ)*ep12567)) ≤ scalar12567.upperTail ∧
    exp (-((12567:ℝ)*em12567)) ≤ scalar12567.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12567:ℝ)) (by norm_num [ep12567]) ?_)
      (show bp12567^8 ≤ scalar12567.upperTail by norm_num [bp12567, scalar12567])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12567, bp12567, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12567:ℝ)) (by norm_num [em12567]) ?_)
      (show bm12567^8 ≤ scalar12567.lowerTail by norm_num [bm12567, scalar12567])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12567, bm12567, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12567 :
    agent12567.root+dsL+scalar12567.worldRadius < √(1/100/aL) ∧
    2*(agent12567.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12567, agent12567, scalar12567, tp12567, tm12567, ep12567, em12567, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12567, agent12567, scalar12567, tp12567, tm12567, ep12567, em12567, dsL]

noncomputable def master12567 : MasterCertificate 12567 world12567 agent12567 :=
  master scalar12567 dsL tp12567 tm12567 ep12567 em12567
    (by norm_num [dsL]) (by norm_num [tp12567]) (by norm_num [tm12567])
    (by norm_num [ep12567]) (by norm_num [em12567])
    positive12567 negative12567 tails12567.1 tails12567.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12567.1 tailGuards12567.2

theorem preserves12567 : master12567.toScalarCertificate = scalar12567 := rfl

noncomputable def tp12568 : ℝ := (115194537 / 500000000)
noncomputable def tm12568 : ℝ := (-((377181807 / 625000000)))
noncomputable def ep12568 : ℝ := (25524125921851979 / 50000000000000000000)
noncomputable def em12568 : ℝ := (6222691701189349 / 12500000000000000000)
noncomputable def bp12568 : ℝ := (22422276896193104349 / 50000000000000000000)
noncomputable def bm12568 : ℝ := (45745905615918416627 / 100000000000000000000)

theorem positive12568 :
    Eplus aL (agent12568.root+dsL) scalar12568.worldRadius world12568.frame
      agent12568.frame tp12568 ≤ -ep12568 := by
  apply positive_check (eT := (115553456092356518007 / 100000000000000000000)) (y := (3776329556240758097 / 10000000000000000000)) (u := (29176547804139839691 / 20000000000000000000))
  · norm_num [world12568, agent12568, scalar12568, tp12568, tm12568, ep12568, em12568, dsL]
  · norm_num [world12568, agent12568, scalar12568, tp12568, tm12568, ep12568, em12568, dsL]
  · norm_num [world12568, agent12568, scalar12568, tp12568, tm12568, ep12568, em12568, dsL]
  · norm_num [world12568, agent12568, scalar12568, tp12568, tm12568, ep12568, em12568, dsL]
  · norm_num [world12568, agent12568, scalar12568, tp12568, tm12568, ep12568, em12568, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12568, agent12568, tp12568, tm12568, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12568, agent12568, scalar12568, tp12568, tm12568, ep12568, em12568, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12568, agent12568, tp12568, tm12568, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12568, agent12568, scalar12568, tp12568, tm12568, ep12568, em12568, dsL]

theorem negative12568 :
    Eminus aL (agent12568.root+dsL) scalar12568.worldRadius world12568.frame
      agent12568.frame tm12568 ≤ -em12568 := by
  apply negative_check (lo := (8559605015458702133 / 12500000000000000000)) (hi := (13695368024733923413 / 20000000000000000000))
    (y := (-((71700952980235159471 / 100000000000000000000)))) (u := (48821005273755467217 / 100000000000000000000))
  · norm_num [world12568, agent12568, scalar12568, tp12568, tm12568, ep12568, em12568, dsL]
  · norm_num [world12568, agent12568, scalar12568, tp12568, tm12568, ep12568, em12568, dsL]
  · norm_num [world12568, agent12568, scalar12568, tp12568, tm12568, ep12568, em12568, dsL]
  · norm_num [world12568, agent12568, scalar12568, tp12568, tm12568, ep12568, em12568, dsL]
  · norm_num [world12568, agent12568, scalar12568, tp12568, tm12568, ep12568, em12568, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12568, agent12568, tp12568, tm12568, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12568, agent12568, tp12568, tm12568, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12568, agent12568, scalar12568, tp12568, tm12568, ep12568, em12568, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12568, agent12568, tp12568, tm12568, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12568, agent12568, scalar12568, tp12568, tm12568, ep12568, em12568, dsL]

theorem tails12568 :
    exp (-((12568:ℝ)*ep12568)) ≤ scalar12568.upperTail ∧
    exp (-((12568:ℝ)*em12568)) ≤ scalar12568.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12568:ℝ)) (by norm_num [ep12568]) ?_)
      (show bp12568^8 ≤ scalar12568.upperTail by norm_num [bp12568, scalar12568])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12568, bp12568, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12568:ℝ)) (by norm_num [em12568]) ?_)
      (show bm12568^8 ≤ scalar12568.lowerTail by norm_num [bm12568, scalar12568])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12568, bm12568, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12568 :
    agent12568.root+dsL+scalar12568.worldRadius < √(1/100/aL) ∧
    2*(agent12568.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12568, agent12568, scalar12568, tp12568, tm12568, ep12568, em12568, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12568, agent12568, scalar12568, tp12568, tm12568, ep12568, em12568, dsL]

noncomputable def master12568 : MasterCertificate 12568 world12568 agent12568 :=
  master scalar12568 dsL tp12568 tm12568 ep12568 em12568
    (by norm_num [dsL]) (by norm_num [tp12568]) (by norm_num [tm12568])
    (by norm_num [ep12568]) (by norm_num [em12568])
    positive12568 negative12568 tails12568.1 tails12568.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12568.1 tailGuards12568.2

theorem preserves12568 : master12568.toScalarCertificate = scalar12568 := rfl

noncomputable def tp12569 : ℝ := (1151990131 / 5000000000)
noncomputable def tm12569 : ℝ := (-((3017550907 / 5000000000)))
noncomputable def ep12569 : ℝ := (25525507395275541 / 50000000000000000000)
noncomputable def em12569 : ℝ := (49783913523003603 / 100000000000000000000)
noncomputable def bp12569 : ℝ := (44839745832179275527 / 100000000000000000000)
noncomputable def bm12569 : ℝ := (45741348712047290813 / 100000000000000000000)

theorem positive12569 :
    Eplus aL (agent12569.root+dsL) scalar12569.worldRadius world12569.frame
      agent12569.frame tp12569 ≤ -ep12569 := by
  apply positive_check (eT := (115553728724524382809 / 100000000000000000000)) (y := (4720516527485122521 / 12500000000000000000)) (u := (72941979782321746763 / 50000000000000000000))
  · norm_num [world12569, agent12569, scalar12569, tp12569, tm12569, ep12569, em12569, dsL]
  · norm_num [world12569, agent12569, scalar12569, tp12569, tm12569, ep12569, em12569, dsL]
  · norm_num [world12569, agent12569, scalar12569, tp12569, tm12569, ep12569, em12569, dsL]
  · norm_num [world12569, agent12569, scalar12569, tp12569, tm12569, ep12569, em12569, dsL]
  · norm_num [world12569, agent12569, scalar12569, tp12569, tm12569, ep12569, em12569, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12569, agent12569, tp12569, tm12569, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12569, agent12569, scalar12569, tp12569, tm12569, ep12569, em12569, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12569, agent12569, tp12569, tm12569, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12569, agent12569, scalar12569, tp12569, tm12569, ep12569, em12569, dsL]

theorem negative12569 :
    Eminus aL (agent12569.root+dsL) scalar12569.worldRadius world12569.frame
      agent12569.frame tm12569 ≤ -em12569 := by
  apply negative_check (lo := (68476595645566607467 / 100000000000000000000)) (hi := (17119148911391651867 / 25000000000000000000))
    (y := (-((35850537633548484219 / 50000000000000000000)))) (u := (48820945572116717989 / 100000000000000000000))
  · norm_num [world12569, agent12569, scalar12569, tp12569, tm12569, ep12569, em12569, dsL]
  · norm_num [world12569, agent12569, scalar12569, tp12569, tm12569, ep12569, em12569, dsL]
  · norm_num [world12569, agent12569, scalar12569, tp12569, tm12569, ep12569, em12569, dsL]
  · norm_num [world12569, agent12569, scalar12569, tp12569, tm12569, ep12569, em12569, dsL]
  · norm_num [world12569, agent12569, scalar12569, tp12569, tm12569, ep12569, em12569, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12569, agent12569, tp12569, tm12569, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12569, agent12569, tp12569, tm12569, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12569, agent12569, scalar12569, tp12569, tm12569, ep12569, em12569, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12569, agent12569, tp12569, tm12569, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12569, agent12569, scalar12569, tp12569, tm12569, ep12569, em12569, dsL]

theorem tails12569 :
    exp (-((12569:ℝ)*ep12569)) ≤ scalar12569.upperTail ∧
    exp (-((12569:ℝ)*em12569)) ≤ scalar12569.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12569:ℝ)) (by norm_num [ep12569]) ?_)
      (show bp12569^8 ≤ scalar12569.upperTail by norm_num [bp12569, scalar12569])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12569, bp12569, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12569:ℝ)) (by norm_num [em12569]) ?_)
      (show bm12569^8 ≤ scalar12569.lowerTail by norm_num [bm12569, scalar12569])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12569, bm12569, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12569 :
    agent12569.root+dsL+scalar12569.worldRadius < √(1/100/aL) ∧
    2*(agent12569.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12569, agent12569, scalar12569, tp12569, tm12569, ep12569, em12569, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12569, agent12569, scalar12569, tp12569, tm12569, ep12569, em12569, dsL]

noncomputable def master12569 : MasterCertificate 12569 world12569 agent12569 :=
  master scalar12569 dsL tp12569 tm12569 ep12569 em12569
    (by norm_num [dsL]) (by norm_num [tp12569]) (by norm_num [tm12569])
    (by norm_num [ep12569]) (by norm_num [em12569])
    positive12569 negative12569 tails12569.1 tails12569.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12569.1 tailGuards12569.2

theorem preserves12569 : master12569.toScalarCertificate = scalar12569 := rfl

noncomputable def tp12570 : ℝ := (2304145189 / 10000000000)
noncomputable def tm12570 : ℝ := (-((188610091 / 312500000)))
noncomputable def ep12570 : ℝ := (25527612690983167 / 50000000000000000000)
noncomputable def em12570 : ℝ := (49787869399493783 / 100000000000000000000)
noncomputable def bp12570 : ℝ := (5604239783586206829 / 12500000000000000000)
noncomputable def bm12570 : ℝ := (45735659454985157281 / 100000000000000000000)

theorem positive12570 :
    Eplus aL (agent12570.root+dsL) scalar12570.worldRadius world12570.frame
      agent12570.frame tp12570 ≤ -ep12570 := by
  apply positive_check (eT := (115554548105560643861 / 100000000000000000000)) (y := (18882118785589952851 / 50000000000000000000)) (u := (145884113255370776453 / 100000000000000000000))
  · norm_num [world12570, agent12570, scalar12570, tp12570, tm12570, ep12570, em12570, dsL]
  · norm_num [world12570, agent12570, scalar12570, tp12570, tm12570, ep12570, em12570, dsL]
  · norm_num [world12570, agent12570, scalar12570, tp12570, tm12570, ep12570, em12570, dsL]
  · norm_num [world12570, agent12570, scalar12570, tp12570, tm12570, ep12570, em12570, dsL]
  · norm_num [world12570, agent12570, scalar12570, tp12570, tm12570, ep12570, em12570, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12570, agent12570, tp12570, tm12570, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12570, agent12570, scalar12570, tp12570, tm12570, ep12570, em12570, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12570, agent12570, tp12570, tm12570, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12570, agent12570, scalar12570, tp12570, tm12570, ep12570, em12570, dsL]

theorem negative12570 :
    Eminus aL (agent12570.root+dsL) scalar12570.worldRadius world12570.frame
      agent12570.frame tm12570 ≤ -em12570 := by
  apply negative_check (lo := (68475370669887377013 / 100000000000000000000)) (hi := (34237685334943688507 / 50000000000000000000))
    (y := (-((35849637232437873553 / 50000000000000000000)))) (u := (12205456187176273483 / 25000000000000000000))
  · norm_num [world12570, agent12570, scalar12570, tp12570, tm12570, ep12570, em12570, dsL]
  · norm_num [world12570, agent12570, scalar12570, tp12570, tm12570, ep12570, em12570, dsL]
  · norm_num [world12570, agent12570, scalar12570, tp12570, tm12570, ep12570, em12570, dsL]
  · norm_num [world12570, agent12570, scalar12570, tp12570, tm12570, ep12570, em12570, dsL]
  · norm_num [world12570, agent12570, scalar12570, tp12570, tm12570, ep12570, em12570, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12570, agent12570, tp12570, tm12570, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12570, agent12570, tp12570, tm12570, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12570, agent12570, scalar12570, tp12570, tm12570, ep12570, em12570, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12570, agent12570, tp12570, tm12570, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12570, agent12570, scalar12570, tp12570, tm12570, ep12570, em12570, dsL]

theorem tails12570 :
    exp (-((12570:ℝ)*ep12570)) ≤ scalar12570.upperTail ∧
    exp (-((12570:ℝ)*em12570)) ≤ scalar12570.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12570:ℝ)) (by norm_num [ep12570]) ?_)
      (show bp12570^8 ≤ scalar12570.upperTail by norm_num [bp12570, scalar12570])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12570, bp12570, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12570:ℝ)) (by norm_num [em12570]) ?_)
      (show bm12570^8 ≤ scalar12570.lowerTail by norm_num [bm12570, scalar12570])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12570, bm12570, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12570 :
    agent12570.root+dsL+scalar12570.worldRadius < √(1/100/aL) ∧
    2*(agent12570.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12570, agent12570, scalar12570, tp12570, tm12570, ep12570, em12570, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12570, agent12570, scalar12570, tp12570, tm12570, ep12570, em12570, dsL]

noncomputable def master12570 : MasterCertificate 12570 world12570 agent12570 :=
  master scalar12570 dsL tp12570 tm12570 ep12570 em12570
    (by norm_num [dsL]) (by norm_num [tp12570]) (by norm_num [tm12570])
    (by norm_num [ep12570]) (by norm_num [em12570])
    positive12570 negative12570 tails12570.1 tails12570.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12570.1 tailGuards12570.2

theorem preserves12570 : master12570.toScalarCertificate = scalar12570 := rfl

noncomputable def tp12571 : ℝ := (2304234539 / 10000000000)
noncomputable def tm12571 : ℝ := (-((6035715497 / 10000000000)))
noncomputable def ep12571 : ℝ := (12764496118828051 / 25000000000000000000)
noncomputable def em12571 : ℝ := (49790245767206771 / 100000000000000000000)
noncomputable def bp12571 : ℝ := (8965822692574210957 / 20000000000000000000)
noncomputable def bm12571 : ℝ := (45731105485519975681 / 100000000000000000000)

theorem positive12571 :
    Eplus aL (agent12571.root+dsL) scalar12571.worldRadius world12571.frame
      agent12571.frame tp12571 ≤ -ep12571 := by
  apply positive_check (eT := (115554819544777703501 / 100000000000000000000)) (y := (2360317002949283853 / 6250000000000000000)) (u := (145885330628375639581 / 100000000000000000000))
  · norm_num [world12571, agent12571, scalar12571, tp12571, tm12571, ep12571, em12571, dsL]
  · norm_num [world12571, agent12571, scalar12571, tp12571, tm12571, ep12571, em12571, dsL]
  · norm_num [world12571, agent12571, scalar12571, tp12571, tm12571, ep12571, em12571, dsL]
  · norm_num [world12571, agent12571, scalar12571, tp12571, tm12571, ep12571, em12571, dsL]
  · norm_num [world12571, agent12571, scalar12571, tp12571, tm12571, ep12571, em12571, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12571, agent12571, tp12571, tm12571, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12571, agent12571, scalar12571, tp12571, tm12571, ep12571, em12571, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12571, agent12571, tp12571, tm12571, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12571, agent12571, scalar12571, tp12571, tm12571, ep12571, em12571, dsL]

theorem negative12571 :
    Eminus aL (agent12571.root+dsL) scalar12571.worldRadius world12571.frame
      agent12571.frame tm12571 ≤ -em12571 := by
  apply negative_check (lo := (34237563732932996197 / 50000000000000000000)) (hi := (13695025493173198479 / 20000000000000000000))
    (y := (-((71699394784968937301 / 100000000000000000000)))) (u := (6102720750784424827 / 12500000000000000000))
  · norm_num [world12571, agent12571, scalar12571, tp12571, tm12571, ep12571, em12571, dsL]
  · norm_num [world12571, agent12571, scalar12571, tp12571, tm12571, ep12571, em12571, dsL]
  · norm_num [world12571, agent12571, scalar12571, tp12571, tm12571, ep12571, em12571, dsL]
  · norm_num [world12571, agent12571, scalar12571, tp12571, tm12571, ep12571, em12571, dsL]
  · norm_num [world12571, agent12571, scalar12571, tp12571, tm12571, ep12571, em12571, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12571, agent12571, tp12571, tm12571, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12571, agent12571, tp12571, tm12571, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12571, agent12571, scalar12571, tp12571, tm12571, ep12571, em12571, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12571, agent12571, tp12571, tm12571, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12571, agent12571, scalar12571, tp12571, tm12571, ep12571, em12571, dsL]

theorem tails12571 :
    exp (-((12571:ℝ)*ep12571)) ≤ scalar12571.upperTail ∧
    exp (-((12571:ℝ)*em12571)) ≤ scalar12571.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12571:ℝ)) (by norm_num [ep12571]) ?_)
      (show bp12571^8 ≤ scalar12571.upperTail by norm_num [bp12571, scalar12571])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12571, bp12571, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12571:ℝ)) (by norm_num [em12571]) ?_)
      (show bm12571^8 ≤ scalar12571.lowerTail by norm_num [bm12571, scalar12571])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12571, bm12571, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12571 :
    agent12571.root+dsL+scalar12571.worldRadius < √(1/100/aL) ∧
    2*(agent12571.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12571, agent12571, scalar12571, tp12571, tm12571, ep12571, em12571, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12571, agent12571, scalar12571, tp12571, tm12571, ep12571, em12571, dsL]

noncomputable def master12571 : MasterCertificate 12571 world12571 agent12571 :=
  master scalar12571 dsL tp12571 tm12571 ep12571 em12571
    (by norm_num [dsL]) (by norm_num [tp12571]) (by norm_num [tm12571])
    (by norm_num [ep12571]) (by norm_num [em12571])
    positive12571 negative12571 tails12571.1 tails12571.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12571.1 tailGuards12571.2

theorem preserves12571 : master12571.toScalarCertificate = scalar12571 := rfl

noncomputable def tp12572 : ℝ := (2304323841 / 10000000000)
noncomputable def tm12572 : ℝ := (-((1508977001 / 2500000000)))
noncomputable def ep12572 : ℝ := (199456025853289 / 390625000000000000)
noncomputable def em12572 : ℝ := (24896310621367129 / 50000000000000000000)
noncomputable def bp12572 : ℝ := (11206077383034513323 / 25000000000000000000)
noncomputable def bm12572 : ℝ := (45726552338960781643 / 100000000000000000000)

theorem positive12572 :
    Eplus aL (agent12572.root+dsL) scalar12572.worldRadius world12572.frame
      agent12572.frame tp12572 ≤ -ep12572 := by
  apply positive_check (eT := (57777545334273472933 / 50000000000000000000)) (y := (37765906124054868949 / 100000000000000000000)) (u := (72943273714622148091 / 50000000000000000000))
  · norm_num [world12572, agent12572, scalar12572, tp12572, tm12572, ep12572, em12572, dsL]
  · norm_num [world12572, agent12572, scalar12572, tp12572, tm12572, ep12572, em12572, dsL]
  · norm_num [world12572, agent12572, scalar12572, tp12572, tm12572, ep12572, em12572, dsL]
  · norm_num [world12572, agent12572, scalar12572, tp12572, tm12572, ep12572, em12572, dsL]
  · norm_num [world12572, agent12572, scalar12572, tp12572, tm12572, ep12572, em12572, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12572, agent12572, tp12572, tm12572, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12572, agent12572, scalar12572, tp12572, tm12572, ep12572, em12572, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12572, agent12572, tp12572, tm12572, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12572, agent12572, scalar12572, tp12572, tm12572, ep12572, em12572, dsL]

theorem negative12572 :
    Eminus aL (agent12572.root+dsL) scalar12572.worldRadius world12572.frame
      agent12572.frame tm12572 ≤ -em12572 := by
  apply negative_check (lo := (85593605675303183 / 125000000000000000)) (hi := (68474884540242546401 / 100000000000000000000))
    (y := (-((35849757685124278831 / 50000000000000000000)))) (u := (48821707134447839737 / 100000000000000000000))
  · norm_num [world12572, agent12572, scalar12572, tp12572, tm12572, ep12572, em12572, dsL]
  · norm_num [world12572, agent12572, scalar12572, tp12572, tm12572, ep12572, em12572, dsL]
  · norm_num [world12572, agent12572, scalar12572, tp12572, tm12572, ep12572, em12572, dsL]
  · norm_num [world12572, agent12572, scalar12572, tp12572, tm12572, ep12572, em12572, dsL]
  · norm_num [world12572, agent12572, scalar12572, tp12572, tm12572, ep12572, em12572, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12572, agent12572, tp12572, tm12572, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12572, agent12572, tp12572, tm12572, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12572, agent12572, scalar12572, tp12572, tm12572, ep12572, em12572, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12572, agent12572, tp12572, tm12572, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12572, agent12572, scalar12572, tp12572, tm12572, ep12572, em12572, dsL]

theorem tails12572 :
    exp (-((12572:ℝ)*ep12572)) ≤ scalar12572.upperTail ∧
    exp (-((12572:ℝ)*em12572)) ≤ scalar12572.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12572:ℝ)) (by norm_num [ep12572]) ?_)
      (show bp12572^8 ≤ scalar12572.upperTail by norm_num [bp12572, scalar12572])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12572, bp12572, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12572:ℝ)) (by norm_num [em12572]) ?_)
      (show bm12572^8 ≤ scalar12572.lowerTail by norm_num [bm12572, scalar12572])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12572, bm12572, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12572 :
    agent12572.root+dsL+scalar12572.worldRadius < √(1/100/aL) ∧
    2*(agent12572.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12572, agent12572, scalar12572, tp12572, tm12572, ep12572, em12572, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12572, agent12572, scalar12572, tp12572, tm12572, ep12572, em12572, dsL]

noncomputable def master12572 : MasterCertificate 12572 world12572 agent12572 :=
  master scalar12572 dsL tp12572 tm12572 ep12572 em12572
    (by norm_num [dsL]) (by norm_num [tp12572]) (by norm_num [tm12572])
    (by norm_num [ep12572]) (by norm_num [em12572])
    positive12572 negative12572 tails12572.1 tails12572.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12572.1 tailGuards12572.2

theorem preserves12572 : master12572.toScalarCertificate = scalar12572 := rfl

noncomputable def tp12573 : ℝ := (230441313 / 1000000000)
noncomputable def tm12573 : ℝ := (-((754512561 / 1250000000)))
noncomputable def ep12573 : ℝ := (51063499478804777 / 100000000000000000000)
noncomputable def em12573 : ℝ := (2489749776791261 / 5000000000000000000)
noncomputable def bp12573 : ℝ := (175076198088775129 / 390625000000000000)
noncomputable def bm12573 : ℝ := (914440004477463089 / 2000000000000000000)

theorem positive12573 :
    Eplus aL (agent12573.root+dsL) scalar12573.worldRadius world12573.frame
      agent12573.frame tp12573 ≤ -ep12573 := by
  apply positive_check (eT := (28888840432668149167 / 25000000000000000000)) (y := (94416850787312667 / 250000000000000000)) (u := (2917755288131594953 / 2000000000000000000))
  · norm_num [world12573, agent12573, scalar12573, tp12573, tm12573, ep12573, em12573, dsL]
  · norm_num [world12573, agent12573, scalar12573, tp12573, tm12573, ep12573, em12573, dsL]
  · norm_num [world12573, agent12573, scalar12573, tp12573, tm12573, ep12573, em12573, dsL]
  · norm_num [world12573, agent12573, scalar12573, tp12573, tm12573, ep12573, em12573, dsL]
  · norm_num [world12573, agent12573, scalar12573, tp12573, tm12573, ep12573, em12573, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12573, agent12573, tp12573, tm12573, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12573, agent12573, scalar12573, tp12573, tm12573, ep12573, em12573, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12573, agent12573, tp12573, tm12573, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12573, agent12573, scalar12573, tp12573, tm12573, ep12573, em12573, dsL]

theorem negative12573 :
    Eminus aL (agent12573.root+dsL) scalar12573.worldRadius world12573.frame
      agent12573.frame tm12573 ≤ -em12573 := by
  apply negative_check (lo := (68474641656654484201 / 100000000000000000000)) (hi := (34237320828327242101 / 50000000000000000000))
    (y := (-((71699636341647706693 / 100000000000000000000)))) (u := (1952865922967254151 / 4000000000000000000))
  · norm_num [world12573, agent12573, scalar12573, tp12573, tm12573, ep12573, em12573, dsL]
  · norm_num [world12573, agent12573, scalar12573, tp12573, tm12573, ep12573, em12573, dsL]
  · norm_num [world12573, agent12573, scalar12573, tp12573, tm12573, ep12573, em12573, dsL]
  · norm_num [world12573, agent12573, scalar12573, tp12573, tm12573, ep12573, em12573, dsL]
  · norm_num [world12573, agent12573, scalar12573, tp12573, tm12573, ep12573, em12573, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12573, agent12573, tp12573, tm12573, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12573, agent12573, tp12573, tm12573, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12573, agent12573, scalar12573, tp12573, tm12573, ep12573, em12573, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12573, agent12573, tp12573, tm12573, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12573, agent12573, scalar12573, tp12573, tm12573, ep12573, em12573, dsL]

theorem tails12573 :
    exp (-((12573:ℝ)*ep12573)) ≤ scalar12573.upperTail ∧
    exp (-((12573:ℝ)*em12573)) ≤ scalar12573.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12573:ℝ)) (by norm_num [ep12573]) ?_)
      (show bp12573^8 ≤ scalar12573.upperTail by norm_num [bp12573, scalar12573])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12573, bp12573, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12573:ℝ)) (by norm_num [em12573]) ?_)
      (show bm12573^8 ≤ scalar12573.lowerTail by norm_num [bm12573, scalar12573])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12573, bm12573, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12573 :
    agent12573.root+dsL+scalar12573.worldRadius < √(1/100/aL) ∧
    2*(agent12573.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12573, agent12573, scalar12573, tp12573, tm12573, ep12573, em12573, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12573, agent12573, scalar12573, tp12573, tm12573, ep12573, em12573, dsL]

noncomputable def master12573 : MasterCertificate 12573 world12573 agent12573 :=
  master scalar12573 dsL tp12573 tm12573 ep12573 em12573
    (by norm_num [dsL]) (by norm_num [tp12573]) (by norm_num [tm12573])
    (by norm_num [ep12573]) (by norm_num [em12573])
    positive12573 negative12573 tails12573.1 tails12573.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12573.1 tailGuards12573.2

theorem preserves12573 : master12573.toScalarCertificate = scalar12573 := rfl

noncomputable def tp12574 : ℝ := (2304502359 / 10000000000)
noncomputable def tm12574 : ℝ := (-((6036292887 / 10000000000)))
noncomputable def ep12574 : ℝ := (6383281904400087 / 12500000000000000000)
noncomputable def em12574 : ℝ := (49797368771934233 / 100000000000000000000)
noncomputable def bp12574 : ℝ := (44814704872663145087 / 100000000000000000000)
noncomputable def bm12574 : ℝ := (22858724525047434869 / 50000000000000000000)

theorem positive12574 :
    Eplus aL (agent12574.root+dsL) scalar12574.worldRadius world12574.frame
      agent12574.frame tp12574 ≤ -ep12574 := by
  apply positive_check (eT := (7222227024399938561 / 6250000000000000000)) (y := (9441893486204921021 / 25000000000000000000)) (u := (18236122571958199653 / 12500000000000000000))
  · norm_num [world12574, agent12574, scalar12574, tp12574, tm12574, ep12574, em12574, dsL]
  · norm_num [world12574, agent12574, scalar12574, tp12574, tm12574, ep12574, em12574, dsL]
  · norm_num [world12574, agent12574, scalar12574, tp12574, tm12574, ep12574, em12574, dsL]
  · norm_num [world12574, agent12574, scalar12574, tp12574, tm12574, ep12574, em12574, dsL]
  · norm_num [world12574, agent12574, scalar12574, tp12574, tm12574, ep12574, em12574, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12574, agent12574, tp12574, tm12574, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12574, agent12574, scalar12574, tp12574, tm12574, ep12574, em12574, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12574, agent12574, tp12574, tm12574, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12574, agent12574, scalar12574, tp12574, tm12574, ep12574, em12574, dsL]

theorem negative12574 :
    Eminus aL (agent12574.root+dsL) scalar12574.worldRadius world12574.frame
      agent12574.frame tm12574 ≤ -em12574 := by
  apply negative_check (lo := (34237199540739688389 / 50000000000000000000)) (hi := (68474399081479376779 / 100000000000000000000))
    (y := (-((71699757383960105011 / 100000000000000000000)))) (u := (48821588979365338691 / 100000000000000000000))
  · norm_num [world12574, agent12574, scalar12574, tp12574, tm12574, ep12574, em12574, dsL]
  · norm_num [world12574, agent12574, scalar12574, tp12574, tm12574, ep12574, em12574, dsL]
  · norm_num [world12574, agent12574, scalar12574, tp12574, tm12574, ep12574, em12574, dsL]
  · norm_num [world12574, agent12574, scalar12574, tp12574, tm12574, ep12574, em12574, dsL]
  · norm_num [world12574, agent12574, scalar12574, tp12574, tm12574, ep12574, em12574, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12574, agent12574, tp12574, tm12574, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12574, agent12574, tp12574, tm12574, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12574, agent12574, scalar12574, tp12574, tm12574, ep12574, em12574, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12574, agent12574, tp12574, tm12574, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12574, agent12574, scalar12574, tp12574, tm12574, ep12574, em12574, dsL]

theorem tails12574 :
    exp (-((12574:ℝ)*ep12574)) ≤ scalar12574.upperTail ∧
    exp (-((12574:ℝ)*em12574)) ≤ scalar12574.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12574:ℝ)) (by norm_num [ep12574]) ?_)
      (show bp12574^8 ≤ scalar12574.upperTail by norm_num [bp12574, scalar12574])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12574, bp12574, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12574:ℝ)) (by norm_num [em12574]) ?_)
      (show bm12574^8 ≤ scalar12574.lowerTail by norm_num [bm12574, scalar12574])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12574, bm12574, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12574 :
    agent12574.root+dsL+scalar12574.worldRadius < √(1/100/aL) ∧
    2*(agent12574.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12574, agent12574, scalar12574, tp12574, tm12574, ep12574, em12574, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12574, agent12574, scalar12574, tp12574, tm12574, ep12574, em12574, dsL]

noncomputable def master12574 : MasterCertificate 12574 world12574 agent12574 :=
  master scalar12574 dsL tp12574 tm12574 ep12574 em12574
    (by norm_num [dsL]) (by norm_num [tp12574]) (by norm_num [tm12574])
    (by norm_num [ep12574]) (by norm_num [em12574])
    positive12574 negative12574 tails12574.1 tails12574.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12574.1 tailGuards12574.2

theorem preserves12574 : master12574.toScalarCertificate = scalar12574 := rfl

end BstLean.Part268
