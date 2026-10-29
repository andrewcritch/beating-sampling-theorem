import BstLean.Part261Checker
import BstLean.Part268Scalar10
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12600 : ℝ := (288380423 / 1250000000)
noncomputable def tm12600 : ℝ := (-((6041960373 / 10000000000)))
noncomputable def ep12600 : ℝ := (51142135009343609 / 100000000000000000000)
noncomputable def em12600 : ℝ := (49863663382900697 / 100000000000000000000)
noncomputable def bp12600 : ℝ := (22343476048015157447 / 50000000000000000000)
noncomputable def bm12600 : ℝ := (9119177150348964621 / 20000000000000000000)

theorem positive12600 :
    Eplus aL (agent12600.root+dsL) scalar12600.worldRadius world12600.frame
      agent12600.frame tp12600 ≤ -ep12600 := by
  apply positive_check (eT := (11556428286107167279 / 10000000000000000000)) (y := (9446774032555597283 / 25000000000000000000)) (u := (36479366018286456519 / 25000000000000000000))
  · norm_num [world12600, agent12600, scalar12600, tp12600, tm12600, ep12600, em12600, dsL]
  · norm_num [world12600, agent12600, scalar12600, tp12600, tm12600, ep12600, em12600, dsL]
  · norm_num [world12600, agent12600, scalar12600, tp12600, tm12600, ep12600, em12600, dsL]
  · norm_num [world12600, agent12600, scalar12600, tp12600, tm12600, ep12600, em12600, dsL]
  · norm_num [world12600, agent12600, scalar12600, tp12600, tm12600, ep12600, em12600, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12600, agent12600, tp12600, tm12600, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12600, agent12600, scalar12600, tp12600, tm12600, ep12600, em12600, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12600, agent12600, tp12600, tm12600, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12600, agent12600, scalar12600, tp12600, tm12600, ep12600, em12600, dsL]

theorem negative12600 :
    Eminus aL (agent12600.root+dsL) scalar12600.worldRadius world12600.frame
      agent12600.frame tm12600 ≤ -em12600 := by
  apply negative_check (lo := (68465216920892026297 / 100000000000000000000)) (hi := (34232608460446013149 / 50000000000000000000))
    (y := (-((35848558234440184227 / 50000000000000000000)))) (u := (48822878333096155367 / 100000000000000000000))
  · norm_num [world12600, agent12600, scalar12600, tp12600, tm12600, ep12600, em12600, dsL]
  · norm_num [world12600, agent12600, scalar12600, tp12600, tm12600, ep12600, em12600, dsL]
  · norm_num [world12600, agent12600, scalar12600, tp12600, tm12600, ep12600, em12600, dsL]
  · norm_num [world12600, agent12600, scalar12600, tp12600, tm12600, ep12600, em12600, dsL]
  · norm_num [world12600, agent12600, scalar12600, tp12600, tm12600, ep12600, em12600, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12600, agent12600, tp12600, tm12600, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12600, agent12600, tp12600, tm12600, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12600, agent12600, scalar12600, tp12600, tm12600, ep12600, em12600, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12600, agent12600, tp12600, tm12600, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12600, agent12600, scalar12600, tp12600, tm12600, ep12600, em12600, dsL]

theorem tails12600 :
    exp (-((12600:ℝ)*ep12600)) ≤ scalar12600.upperTail ∧
    exp (-((12600:ℝ)*em12600)) ≤ scalar12600.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12600:ℝ)) (by norm_num [ep12600]) ?_)
      (show bp12600^8 ≤ scalar12600.upperTail by norm_num [bp12600, scalar12600])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12600, bp12600, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12600:ℝ)) (by norm_num [em12600]) ?_)
      (show bm12600^8 ≤ scalar12600.lowerTail by norm_num [bm12600, scalar12600])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12600, bm12600, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12600 :
    agent12600.root+dsL+scalar12600.worldRadius < √(1/100/aL) ∧
    2*(agent12600.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12600, agent12600, scalar12600, tp12600, tm12600, ep12600, em12600, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12600, agent12600, scalar12600, tp12600, tm12600, ep12600, em12600, dsL]

noncomputable def master12600 : MasterCertificate 12600 world12600 agent12600 :=
  master scalar12600 dsL tp12600 tm12600 ep12600 em12600
    (by norm_num [dsL]) (by norm_num [tp12600]) (by norm_num [tm12600])
    (by norm_num [ep12600]) (by norm_num [em12600])
    positive12600 negative12600 tails12600.1 tails12600.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12600.1 tailGuards12600.2

theorem preserves12600 : master12600.toScalarCertificate = scalar12600 := rfl

noncomputable def tp12601 : ℝ := (1153566189 / 5000000000)
noncomputable def tm12601 : ℝ := (-((6042151997 / 10000000000)))
noncomputable def ep12601 : ℝ := (51144884550703163 / 100000000000000000000)
noncomputable def em12601 : ℝ := (12466507284274103 / 25000000000000000000)
noncomputable def bp12601 : ℝ := (8936432057178636697 / 20000000000000000000)
noncomputable def bm12601 : ℝ := (45591344939292346641 / 100000000000000000000)

theorem positive12601 :
    Eplus aL (agent12601.root+dsL) scalar12601.worldRadius world12601.frame
      agent12601.frame tp12601 ≤ -ep12601 := by
  apply positive_check (eT := (3611392270720563127 / 3125000000000000000)) (y := (47234912550117727 / 125000000000000000)) (u := (29183736179671401399 / 20000000000000000000))
  · norm_num [world12601, agent12601, scalar12601, tp12601, tm12601, ep12601, em12601, dsL]
  · norm_num [world12601, agent12601, scalar12601, tp12601, tm12601, ep12601, em12601, dsL]
  · norm_num [world12601, agent12601, scalar12601, tp12601, tm12601, ep12601, em12601, dsL]
  · norm_num [world12601, agent12601, scalar12601, tp12601, tm12601, ep12601, em12601, dsL]
  · norm_num [world12601, agent12601, scalar12601, tp12601, tm12601, ep12601, em12601, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12601, agent12601, tp12601, tm12601, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12601, agent12601, scalar12601, tp12601, tm12601, ep12601, em12601, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12601, agent12601, tp12601, tm12601, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12601, agent12601, scalar12601, tp12601, tm12601, ep12601, em12601, dsL]

theorem negative12601 :
    Eminus aL (agent12601.root+dsL) scalar12601.worldRadius world12601.frame
      agent12601.frame tm12601 ≤ -em12601 := by
  apply negative_check (lo := (13692995244042121253 / 20000000000000000000)) (hi := (34232488110105303133 / 50000000000000000000))
    (y := (-((71697231576426601821 / 100000000000000000000)))) (u := (24411411067155625083 / 50000000000000000000))
  · norm_num [world12601, agent12601, scalar12601, tp12601, tm12601, ep12601, em12601, dsL]
  · norm_num [world12601, agent12601, scalar12601, tp12601, tm12601, ep12601, em12601, dsL]
  · norm_num [world12601, agent12601, scalar12601, tp12601, tm12601, ep12601, em12601, dsL]
  · norm_num [world12601, agent12601, scalar12601, tp12601, tm12601, ep12601, em12601, dsL]
  · norm_num [world12601, agent12601, scalar12601, tp12601, tm12601, ep12601, em12601, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12601, agent12601, tp12601, tm12601, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12601, agent12601, tp12601, tm12601, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12601, agent12601, scalar12601, tp12601, tm12601, ep12601, em12601, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12601, agent12601, tp12601, tm12601, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12601, agent12601, scalar12601, tp12601, tm12601, ep12601, em12601, dsL]

theorem tails12601 :
    exp (-((12601:ℝ)*ep12601)) ≤ scalar12601.upperTail ∧
    exp (-((12601:ℝ)*em12601)) ≤ scalar12601.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12601:ℝ)) (by norm_num [ep12601]) ?_)
      (show bp12601^8 ≤ scalar12601.upperTail by norm_num [bp12601, scalar12601])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12601, bp12601, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12601:ℝ)) (by norm_num [em12601]) ?_)
      (show bm12601^8 ≤ scalar12601.lowerTail by norm_num [bm12601, scalar12601])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12601, bm12601, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12601 :
    agent12601.root+dsL+scalar12601.worldRadius < √(1/100/aL) ∧
    2*(agent12601.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12601, agent12601, scalar12601, tp12601, tm12601, ep12601, em12601, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12601, agent12601, scalar12601, tp12601, tm12601, ep12601, em12601, dsL]

noncomputable def master12601 : MasterCertificate 12601 world12601 agent12601 :=
  master scalar12601 dsL tp12601 tm12601 ep12601 em12601
    (by norm_num [dsL]) (by norm_num [tp12601]) (by norm_num [tm12601])
    (by norm_num [ep12601]) (by norm_num [em12601])
    positive12601 negative12601 tails12601.1 tails12601.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12601.1 tailGuards12601.2

theorem preserves12601 : master12601.toScalarCertificate = scalar12601 := rfl

noncomputable def tp12602 : ℝ := (2307221331 / 10000000000)
noncomputable def tm12602 : ℝ := (-((6042343447 / 10000000000)))
noncomputable def ep12602 : ℝ := (25573816776154291 / 50000000000000000000)
noncomputable def em12602 : ℝ := (49868394377593483 / 100000000000000000000)
noncomputable def bp12602 : ℝ := (22338684531173750991 / 50000000000000000000)
noncomputable def bm12602 : ℝ := (5698350584790431197 / 12500000000000000000)

theorem positive12602 :
    Eplus aL (agent12602.root+dsL) scalar12602.worldRadius world12602.frame
      agent12602.frame tp12602 ≤ -ep12602 := by
  apply positive_check (eT := (14445602775049848323 / 12500000000000000000)) (y := (37788763517105321833 / 100000000000000000000)) (u := (145919897102085636077 / 100000000000000000000))
  · norm_num [world12602, agent12602, scalar12602, tp12602, tm12602, ep12602, em12602, dsL]
  · norm_num [world12602, agent12602, scalar12602, tp12602, tm12602, ep12602, em12602, dsL]
  · norm_num [world12602, agent12602, scalar12602, tp12602, tm12602, ep12602, em12602, dsL]
  · norm_num [world12602, agent12602, scalar12602, tp12602, tm12602, ep12602, em12602, dsL]
  · norm_num [world12602, agent12602, scalar12602, tp12602, tm12602, ep12602, em12602, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12602, agent12602, tp12602, tm12602, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12602, agent12602, scalar12602, tp12602, tm12602, ep12602, em12602, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12602, agent12602, tp12602, tm12602, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12602, agent12602, scalar12602, tp12602, tm12602, ep12602, em12602, dsL]

theorem negative12602 :
    Eminus aL (agent12602.root+dsL) scalar12602.worldRadius world12602.frame
      agent12602.frame tm12602 ≤ -em12602 := by
  apply negative_check (lo := (68464736209977696151 / 100000000000000000000)) (hi := (8558092026247212019 / 12500000000000000000))
    (y := (-((7169734571514697549 / 10000000000000000000)))) (u := (3051422900537413629 / 6250000000000000000))
  · norm_num [world12602, agent12602, scalar12602, tp12602, tm12602, ep12602, em12602, dsL]
  · norm_num [world12602, agent12602, scalar12602, tp12602, tm12602, ep12602, em12602, dsL]
  · norm_num [world12602, agent12602, scalar12602, tp12602, tm12602, ep12602, em12602, dsL]
  · norm_num [world12602, agent12602, scalar12602, tp12602, tm12602, ep12602, em12602, dsL]
  · norm_num [world12602, agent12602, scalar12602, tp12602, tm12602, ep12602, em12602, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12602, agent12602, tp12602, tm12602, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12602, agent12602, tp12602, tm12602, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12602, agent12602, scalar12602, tp12602, tm12602, ep12602, em12602, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12602, agent12602, tp12602, tm12602, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12602, agent12602, scalar12602, tp12602, tm12602, ep12602, em12602, dsL]

theorem tails12602 :
    exp (-((12602:ℝ)*ep12602)) ≤ scalar12602.upperTail ∧
    exp (-((12602:ℝ)*em12602)) ≤ scalar12602.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12602:ℝ)) (by norm_num [ep12602]) ?_)
      (show bp12602^8 ≤ scalar12602.upperTail by norm_num [bp12602, scalar12602])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12602, bp12602, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12602:ℝ)) (by norm_num [em12602]) ?_)
      (show bm12602^8 ≤ scalar12602.lowerTail by norm_num [bm12602, scalar12602])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12602, bm12602, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12602 :
    agent12602.root+dsL+scalar12602.worldRadius < √(1/100/aL) ∧
    2*(agent12602.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12602, agent12602, scalar12602, tp12602, tm12602, ep12602, em12602, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12602, agent12602, scalar12602, tp12602, tm12602, ep12602, em12602, dsL]

noncomputable def master12602 : MasterCertificate 12602 world12602 agent12602 :=
  master scalar12602 dsL tp12602 tm12602 ep12602 em12602
    (by norm_num [dsL]) (by norm_num [tp12602]) (by norm_num [tm12602])
    (by norm_num [ep12602]) (by norm_num [em12602])
    positive12602 negative12602 tails12602.1 tails12602.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12602.1 tailGuards12602.2

theorem preserves12602 : master12602.toScalarCertificate = scalar12602 := rfl

noncomputable def tp12603 : ℝ := (576827559 / 2500000000)
noncomputable def tm12603 : ℝ := (-((3021267419 / 5000000000)))
noncomputable def ep12603 : ℝ := (5115038076251367 / 10000000000000000000)
noncomputable def em12603 : ℝ := (24935378987859061 / 50000000000000000000)
noncomputable def bp12603 : ℝ := (22336289653132256637 / 50000000000000000000)
noncomputable def bm12603 : ℝ := (911645315586848561 / 2000000000000000000)

theorem positive12603 :
    Eplus aL (agent12603.root+dsL) scalar12603.worldRadius world12603.frame
      agent12603.frame tp12603 ≤ -ep12603 := by
  apply positive_check (eT := (57782545711212947803 / 50000000000000000000)) (y := (2361849789781011971 / 6250000000000000000)) (u := (145921112794107606623 / 100000000000000000000))
  · norm_num [world12603, agent12603, scalar12603, tp12603, tm12603, ep12603, em12603, dsL]
  · norm_num [world12603, agent12603, scalar12603, tp12603, tm12603, ep12603, em12603, dsL]
  · norm_num [world12603, agent12603, scalar12603, tp12603, tm12603, ep12603, em12603, dsL]
  · norm_num [world12603, agent12603, scalar12603, tp12603, tm12603, ep12603, em12603, dsL]
  · norm_num [world12603, agent12603, scalar12603, tp12603, tm12603, ep12603, em12603, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12603, agent12603, tp12603, tm12603, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12603, agent12603, scalar12603, tp12603, tm12603, ep12603, em12603, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12603, agent12603, tp12603, tm12603, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12603, agent12603, scalar12603, tp12603, tm12603, ep12603, em12603, dsL]

theorem negative12603 :
    Eminus aL (agent12603.root+dsL) scalar12603.worldRadius world12603.frame
      agent12603.frame tm12603 ≤ -em12603 := by
  apply negative_check (lo := (68464496396437906463 / 100000000000000000000)) (hi := (2139515512388684577 / 3125000000000000000))
    (y := (-((35848730079987698569 / 50000000000000000000)))) (u := (190713713021481813 / 390625000000000000))
  · norm_num [world12603, agent12603, scalar12603, tp12603, tm12603, ep12603, em12603, dsL]
  · norm_num [world12603, agent12603, scalar12603, tp12603, tm12603, ep12603, em12603, dsL]
  · norm_num [world12603, agent12603, scalar12603, tp12603, tm12603, ep12603, em12603, dsL]
  · norm_num [world12603, agent12603, scalar12603, tp12603, tm12603, ep12603, em12603, dsL]
  · norm_num [world12603, agent12603, scalar12603, tp12603, tm12603, ep12603, em12603, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12603, agent12603, tp12603, tm12603, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12603, agent12603, tp12603, tm12603, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12603, agent12603, scalar12603, tp12603, tm12603, ep12603, em12603, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12603, agent12603, tp12603, tm12603, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12603, agent12603, scalar12603, tp12603, tm12603, ep12603, em12603, dsL]

theorem tails12603 :
    exp (-((12603:ℝ)*ep12603)) ≤ scalar12603.upperTail ∧
    exp (-((12603:ℝ)*em12603)) ≤ scalar12603.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12603:ℝ)) (by norm_num [ep12603]) ?_)
      (show bp12603^8 ≤ scalar12603.upperTail by norm_num [bp12603, scalar12603])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12603, bp12603, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12603:ℝ)) (by norm_num [em12603]) ?_)
      (show bm12603^8 ≤ scalar12603.lowerTail by norm_num [bm12603, scalar12603])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12603, bm12603, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12603 :
    agent12603.root+dsL+scalar12603.worldRadius < √(1/100/aL) ∧
    2*(agent12603.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12603, agent12603, scalar12603, tp12603, tm12603, ep12603, em12603, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12603, agent12603, scalar12603, tp12603, tm12603, ep12603, em12603, dsL]

noncomputable def master12603 : MasterCertificate 12603 world12603 agent12603 :=
  master scalar12603 dsL tp12603 tm12603 ep12603 em12603
    (by norm_num [dsL]) (by norm_num [tp12603]) (by norm_num [tm12603])
    (by norm_num [ep12603]) (by norm_num [em12603])
    positive12603 negative12603 tails12603.1 tails12603.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12603.1 tailGuards12603.2

theorem preserves12603 : master12603.toScalarCertificate = scalar12603 := rfl

noncomputable def tp12604 : ℝ := (2307399057 / 10000000000)
noncomputable def tm12604 : ℝ := (-((6042726031 / 10000000000)))
noncomputable def ep12604 : ℝ := (25576563178432109 / 50000000000000000000)
noncomputable def em12604 : ℝ := (49873120047386553 / 100000000000000000000)
noncomputable def bp12604 : ℝ := (4466779089404368273 / 10000000000000000000)
noncomputable def bm12604 : ℝ := (45577728159076408249 / 100000000000000000000)

theorem positive12604 :
    Eplus aL (agent12604.root+dsL) scalar12604.worldRadius world12604.frame
      agent12604.frame tp12604 ≤ -ep12604 := by
  apply positive_check (eT := (115565360068247591529 / 100000000000000000000)) (y := (37790428815620397959 / 100000000000000000000)) (u := (29184465424839756529 / 20000000000000000000))
  · norm_num [world12604, agent12604, scalar12604, tp12604, tm12604, ep12604, em12604, dsL]
  · norm_num [world12604, agent12604, scalar12604, tp12604, tm12604, ep12604, em12604, dsL]
  · norm_num [world12604, agent12604, scalar12604, tp12604, tm12604, ep12604, em12604, dsL]
  · norm_num [world12604, agent12604, scalar12604, tp12604, tm12604, ep12604, em12604, dsL]
  · norm_num [world12604, agent12604, scalar12604, tp12604, tm12604, ep12604, em12604, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12604, agent12604, tp12604, tm12604, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12604, agent12604, scalar12604, tp12604, tm12604, ep12604, em12604, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12604, agent12604, tp12604, tm12604, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12604, agent12604, scalar12604, tp12604, tm12604, ep12604, em12604, dsL]

theorem negative12604 :
    Eminus aL (agent12604.root+dsL) scalar12604.worldRadius world12604.frame
      agent12604.frame tm12604 ≤ -em12604 := by
  apply negative_check (lo := (34232128688170728657 / 50000000000000000000)) (hi := (13692851475268291463 / 20000000000000000000))
    (y := (-((71697573432447562027 / 100000000000000000000)))) (u := (48822655230839466277 / 100000000000000000000))
  · norm_num [world12604, agent12604, scalar12604, tp12604, tm12604, ep12604, em12604, dsL]
  · norm_num [world12604, agent12604, scalar12604, tp12604, tm12604, ep12604, em12604, dsL]
  · norm_num [world12604, agent12604, scalar12604, tp12604, tm12604, ep12604, em12604, dsL]
  · norm_num [world12604, agent12604, scalar12604, tp12604, tm12604, ep12604, em12604, dsL]
  · norm_num [world12604, agent12604, scalar12604, tp12604, tm12604, ep12604, em12604, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12604, agent12604, tp12604, tm12604, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12604, agent12604, tp12604, tm12604, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12604, agent12604, scalar12604, tp12604, tm12604, ep12604, em12604, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12604, agent12604, tp12604, tm12604, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12604, agent12604, scalar12604, tp12604, tm12604, ep12604, em12604, dsL]

theorem tails12604 :
    exp (-((12604:ℝ)*ep12604)) ≤ scalar12604.upperTail ∧
    exp (-((12604:ℝ)*em12604)) ≤ scalar12604.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12604:ℝ)) (by norm_num [ep12604]) ?_)
      (show bp12604^8 ≤ scalar12604.upperTail by norm_num [bp12604, scalar12604])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12604, bp12604, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12604:ℝ)) (by norm_num [em12604]) ?_)
      (show bm12604^8 ≤ scalar12604.lowerTail by norm_num [bm12604, scalar12604])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12604, bm12604, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12604 :
    agent12604.root+dsL+scalar12604.worldRadius < √(1/100/aL) ∧
    2*(agent12604.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12604, agent12604, scalar12604, tp12604, tm12604, ep12604, em12604, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12604, agent12604, scalar12604, tp12604, tm12604, ep12604, em12604, dsL]

noncomputable def master12604 : MasterCertificate 12604 world12604 agent12604 :=
  master scalar12604 dsL tp12604 tm12604 ep12604 em12604
    (by norm_num [dsL]) (by norm_num [tp12604]) (by norm_num [tm12604])
    (by norm_num [ep12604]) (by norm_num [em12604])
    positive12604 negative12604 tails12604.1 tails12604.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12604.1 tailGuards12604.2

theorem preserves12604 : master12604.toScalarCertificate = scalar12604 := rfl

noncomputable def tp12605 : ℝ := (461497583 / 2000000000)
noncomputable def tm12605 : ℝ := (-((6042917141 / 10000000000)))
noncomputable def ep12605 : ℝ := (51155870775697887 / 100000000000000000000)
noncomputable def em12605 : ℝ := (24937740531597773 / 50000000000000000000)
noncomputable def bp12605 : ℝ := (11165750878939629279 / 25000000000000000000)
noncomputable def bm12605 : ℝ := (22786595739788203527 / 50000000000000000000)

theorem positive12605 :
    Eplus aL (agent12605.root+dsL) scalar12605.worldRadius world12605.frame
      agent12605.frame tp12605 ≤ -ep12605 := by
  apply positive_check (eT := (57782814507314502719 / 50000000000000000000)) (y := (37791261931521623897 / 100000000000000000000)) (u := (145923542831373611137 / 100000000000000000000))
  · norm_num [world12605, agent12605, scalar12605, tp12605, tm12605, ep12605, em12605, dsL]
  · norm_num [world12605, agent12605, scalar12605, tp12605, tm12605, ep12605, em12605, dsL]
  · norm_num [world12605, agent12605, scalar12605, tp12605, tm12605, ep12605, em12605, dsL]
  · norm_num [world12605, agent12605, scalar12605, tp12605, tm12605, ep12605, em12605, dsL]
  · norm_num [world12605, agent12605, scalar12605, tp12605, tm12605, ep12605, em12605, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12605, agent12605, tp12605, tm12605, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12605, agent12605, scalar12605, tp12605, tm12605, ep12605, em12605, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12605, agent12605, tp12605, tm12605, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12605, agent12605, scalar12605, tp12605, tm12605, ep12605, em12605, dsL]

theorem negative12605 :
    Eminus aL (agent12605.root+dsL) scalar12605.worldRadius world12605.frame
      agent12605.frame tm12605 ≤ -em12605 := by
  apply negative_check (lo := (34232009327975298451 / 50000000000000000000)) (hi := (68464018655950596903 / 100000000000000000000))
    (y := (-((71697686616681239271 / 100000000000000000000)))) (u := (6102824996415319363 / 12500000000000000000))
  · norm_num [world12605, agent12605, scalar12605, tp12605, tm12605, ep12605, em12605, dsL]
  · norm_num [world12605, agent12605, scalar12605, tp12605, tm12605, ep12605, em12605, dsL]
  · norm_num [world12605, agent12605, scalar12605, tp12605, tm12605, ep12605, em12605, dsL]
  · norm_num [world12605, agent12605, scalar12605, tp12605, tm12605, ep12605, em12605, dsL]
  · norm_num [world12605, agent12605, scalar12605, tp12605, tm12605, ep12605, em12605, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12605, agent12605, tp12605, tm12605, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12605, agent12605, tp12605, tm12605, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12605, agent12605, scalar12605, tp12605, tm12605, ep12605, em12605, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12605, agent12605, tp12605, tm12605, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12605, agent12605, scalar12605, tp12605, tm12605, ep12605, em12605, dsL]

theorem tails12605 :
    exp (-((12605:ℝ)*ep12605)) ≤ scalar12605.upperTail ∧
    exp (-((12605:ℝ)*em12605)) ≤ scalar12605.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12605:ℝ)) (by norm_num [ep12605]) ?_)
      (show bp12605^8 ≤ scalar12605.upperTail by norm_num [bp12605, scalar12605])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12605, bp12605, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12605:ℝ)) (by norm_num [em12605]) ?_)
      (show bm12605^8 ≤ scalar12605.lowerTail by norm_num [bm12605, scalar12605])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12605, bm12605, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12605 :
    agent12605.root+dsL+scalar12605.worldRadius < √(1/100/aL) ∧
    2*(agent12605.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12605, agent12605, scalar12605, tp12605, tm12605, ep12605, em12605, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12605, agent12605, scalar12605, tp12605, tm12605, ep12605, em12605, dsL]

noncomputable def master12605 : MasterCertificate 12605 world12605 agent12605 :=
  master scalar12605 dsL tp12605 tm12605 ep12605 em12605
    (by norm_num [dsL]) (by norm_num [tp12605]) (by norm_num [tm12605])
    (by norm_num [ep12605]) (by norm_num [em12605])
    positive12605 negative12605 tails12605.1 tails12605.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12605.1 tailGuards12605.2

theorem preserves12605 : master12605.toScalarCertificate = scalar12605 := rfl

noncomputable def tp12606 : ℝ := (576894153 / 2500000000)
noncomputable def tm12606 : ℝ := (-((377694259 / 625000000)))
noncomputable def ep12606 : ℝ := (51158613258359951 / 100000000000000000000)
noncomputable def em12606 : ℝ := (49877840279408993 / 100000000000000000000)
noncomputable def bp12606 : ℝ := (8931643541331519209 / 20000000000000000000)
noncomputable def bm12606 : ℝ := (45568656274870144917 / 100000000000000000000)

theorem positive12606 :
    Eplus aL (agent12606.root+dsL) scalar12606.worldRadius world12606.frame
      agent12606.frame tp12606 ≤ -ep12606 := by
  apply positive_check (eT := (115565896826998988877 / 100000000000000000000)) (y := (37792092751362866729 / 100000000000000000000)) (u := (145924755198156783589 / 100000000000000000000))
  · norm_num [world12606, agent12606, scalar12606, tp12606, tm12606, ep12606, em12606, dsL]
  · norm_num [world12606, agent12606, scalar12606, tp12606, tm12606, ep12606, em12606, dsL]
  · norm_num [world12606, agent12606, scalar12606, tp12606, tm12606, ep12606, em12606, dsL]
  · norm_num [world12606, agent12606, scalar12606, tp12606, tm12606, ep12606, em12606, dsL]
  · norm_num [world12606, agent12606, scalar12606, tp12606, tm12606, ep12606, em12606, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12606, agent12606, tp12606, tm12606, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12606, agent12606, scalar12606, tp12606, tm12606, ep12606, em12606, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12606, agent12606, tp12606, tm12606, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12606, agent12606, scalar12606, tp12606, tm12606, ep12606, em12606, dsL]

theorem negative12606 :
    Eminus aL (agent12606.root+dsL) scalar12606.worldRadius world12606.frame
      agent12606.frame tm12606 ≤ -em12606 := by
  apply negative_check (lo := (34231890169121690321 / 50000000000000000000)) (hi := (68463780338243380643 / 100000000000000000000))
    (y := (-((71697799512648597699 / 100000000000000000000)))) (u := (24411272426303570577 / 50000000000000000000))
  · norm_num [world12606, agent12606, scalar12606, tp12606, tm12606, ep12606, em12606, dsL]
  · norm_num [world12606, agent12606, scalar12606, tp12606, tm12606, ep12606, em12606, dsL]
  · norm_num [world12606, agent12606, scalar12606, tp12606, tm12606, ep12606, em12606, dsL]
  · norm_num [world12606, agent12606, scalar12606, tp12606, tm12606, ep12606, em12606, dsL]
  · norm_num [world12606, agent12606, scalar12606, tp12606, tm12606, ep12606, em12606, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12606, agent12606, tp12606, tm12606, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12606, agent12606, tp12606, tm12606, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12606, agent12606, scalar12606, tp12606, tm12606, ep12606, em12606, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12606, agent12606, tp12606, tm12606, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12606, agent12606, scalar12606, tp12606, tm12606, ep12606, em12606, dsL]

theorem tails12606 :
    exp (-((12606:ℝ)*ep12606)) ≤ scalar12606.upperTail ∧
    exp (-((12606:ℝ)*em12606)) ≤ scalar12606.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12606:ℝ)) (by norm_num [ep12606]) ?_)
      (show bp12606^8 ≤ scalar12606.upperTail by norm_num [bp12606, scalar12606])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12606, bp12606, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12606:ℝ)) (by norm_num [em12606]) ?_)
      (show bm12606^8 ≤ scalar12606.lowerTail by norm_num [bm12606, scalar12606])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12606, bm12606, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12606 :
    agent12606.root+dsL+scalar12606.worldRadius < √(1/100/aL) ∧
    2*(agent12606.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12606, agent12606, scalar12606, tp12606, tm12606, ep12606, em12606, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12606, agent12606, scalar12606, tp12606, tm12606, ep12606, em12606, dsL]

noncomputable def master12606 : MasterCertificate 12606 world12606 agent12606 :=
  master scalar12606 dsL tp12606 tm12606 ep12606 em12606
    (by norm_num [dsL]) (by norm_num [tp12606]) (by norm_num [tm12606])
    (by norm_num [ep12606]) (by norm_num [em12606])
    positive12606 negative12606 tails12606.1 tails12606.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12606.1 tailGuards12606.2

theorem preserves12606 : master12606.toScalarCertificate = scalar12606 := rfl

noncomputable def tp12607 : ℝ := (2307665349 / 10000000000)
noncomputable def tm12607 : ℝ := (-((6043299071 / 10000000000)))
noncomputable def ep12607 : ℝ := (51161355060261047 / 100000000000000000000)
noncomputable def em12607 : ℝ := (49880198834723453 / 100000000000000000000)
noncomputable def bp12607 : ℝ := (44653432583260419953 / 100000000000000000000)
noncomputable def bm12607 : ℝ := (45564121727292284037 / 100000000000000000000)

theorem positive12607 :
    Eplus aL (agent12607.root+dsL) scalar12607.worldRadius world12607.frame
      agent12607.frame tp12607 ≤ -ep12607 := by
  apply positive_check (eT := (14445770620206313657 / 12500000000000000000)) (y := (18896462356955653659 / 50000000000000000000)) (u := (14592596924251912607 / 10000000000000000000))
  · norm_num [world12607, agent12607, scalar12607, tp12607, tm12607, ep12607, em12607, dsL]
  · norm_num [world12607, agent12607, scalar12607, tp12607, tm12607, ep12607, em12607, dsL]
  · norm_num [world12607, agent12607, scalar12607, tp12607, tm12607, ep12607, em12607, dsL]
  · norm_num [world12607, agent12607, scalar12607, tp12607, tm12607, ep12607, em12607, dsL]
  · norm_num [world12607, agent12607, scalar12607, tp12607, tm12607, ep12607, em12607, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12607, agent12607, tp12607, tm12607, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12607, agent12607, scalar12607, tp12607, tm12607, ep12607, em12607, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12607, agent12607, tp12607, tm12607, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12607, agent12607, scalar12607, tp12607, tm12607, ep12607, em12607, dsL]

theorem negative12607 :
    Eminus aL (agent12607.root+dsL) scalar12607.worldRadius world12607.frame
      agent12607.frame tm12607 ≤ -em12607 := by
  apply negative_check (lo := (534871424142204041 / 781250000000000000)) (hi := (68463542290202117249 / 100000000000000000000))
    (y := (-((71697912682141531491 / 100000000000000000000)))) (u := (9764497920082391681 / 20000000000000000000))
  · norm_num [world12607, agent12607, scalar12607, tp12607, tm12607, ep12607, em12607, dsL]
  · norm_num [world12607, agent12607, scalar12607, tp12607, tm12607, ep12607, em12607, dsL]
  · norm_num [world12607, agent12607, scalar12607, tp12607, tm12607, ep12607, em12607, dsL]
  · norm_num [world12607, agent12607, scalar12607, tp12607, tm12607, ep12607, em12607, dsL]
  · norm_num [world12607, agent12607, scalar12607, tp12607, tm12607, ep12607, em12607, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12607, agent12607, tp12607, tm12607, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12607, agent12607, tp12607, tm12607, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12607, agent12607, scalar12607, tp12607, tm12607, ep12607, em12607, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12607, agent12607, tp12607, tm12607, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12607, agent12607, scalar12607, tp12607, tm12607, ep12607, em12607, dsL]

theorem tails12607 :
    exp (-((12607:ℝ)*ep12607)) ≤ scalar12607.upperTail ∧
    exp (-((12607:ℝ)*em12607)) ≤ scalar12607.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12607:ℝ)) (by norm_num [ep12607]) ?_)
      (show bp12607^8 ≤ scalar12607.upperTail by norm_num [bp12607, scalar12607])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12607, bp12607, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12607:ℝ)) (by norm_num [em12607]) ?_)
      (show bm12607^8 ≤ scalar12607.lowerTail by norm_num [bm12607, scalar12607])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12607, bm12607, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12607 :
    agent12607.root+dsL+scalar12607.worldRadius < √(1/100/aL) ∧
    2*(agent12607.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12607, agent12607, scalar12607, tp12607, tm12607, ep12607, em12607, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12607, agent12607, scalar12607, tp12607, tm12607, ep12607, em12607, dsL]

noncomputable def master12607 : MasterCertificate 12607 world12607 agent12607 :=
  master scalar12607 dsL tp12607 tm12607 ep12607 em12607
    (by norm_num [dsL]) (by norm_num [tp12607]) (by norm_num [tm12607])
    (by norm_num [ep12607]) (by norm_num [em12607])
    positive12607 negative12607 tails12607.1 tails12607.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12607.1 tailGuards12607.2

theorem preserves12607 : master12607.toScalarCertificate = scalar12607 := rfl

noncomputable def tp12608 : ℝ := (576938507 / 2500000000)
noncomputable def tm12608 : ℝ := (-((6043489897 / 10000000000)))
noncomputable def ep12608 : ℝ := (1279102368911017 / 2500000000000000000)
noncomputable def em12608 : ℝ := (49882555473091359 / 100000000000000000000)
noncomputable def bp12608 : ℝ := (2232432457413099943 / 5000000000000000000)
noncomputable def bm12608 : ℝ := (22779794369357771383 / 50000000000000000000)

theorem positive12608 :
    Eplus aL (agent12608.root+dsL) scalar12608.worldRadius world12608.frame
      agent12608.frame tp12608 ≤ -ep12608 := by
  apply positive_check (eT := (2889160817714150189 / 2500000000000000000)) (y := (37793756039299042713 / 100000000000000000000)) (u := (145927182367191237781 / 100000000000000000000))
  · norm_num [world12608, agent12608, scalar12608, tp12608, tm12608, ep12608, em12608, dsL]
  · norm_num [world12608, agent12608, scalar12608, tp12608, tm12608, ep12608, em12608, dsL]
  · norm_num [world12608, agent12608, scalar12608, tp12608, tm12608, ep12608, em12608, dsL]
  · norm_num [world12608, agent12608, scalar12608, tp12608, tm12608, ep12608, em12608, dsL]
  · norm_num [world12608, agent12608, scalar12608, tp12608, tm12608, ep12608, em12608, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12608, agent12608, tp12608, tm12608, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12608, agent12608, scalar12608, tp12608, tm12608, ep12608, em12608, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12608, agent12608, tp12608, tm12608, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12608, agent12608, scalar12608, tp12608, tm12608, ep12608, em12608, dsL]

theorem negative12608 :
    Eminus aL (agent12608.root+dsL) scalar12608.worldRadius world12608.frame
      agent12608.frame tm12608 ≤ -em12608 := by
  apply negative_check (lo := (68463304619093926827 / 100000000000000000000)) (hi := (17115826154773481707 / 25000000000000000000))
    (y := (-((17924506332575509643 / 25000000000000000000)))) (u := (24411217301403243341 / 50000000000000000000))
  · norm_num [world12608, agent12608, scalar12608, tp12608, tm12608, ep12608, em12608, dsL]
  · norm_num [world12608, agent12608, scalar12608, tp12608, tm12608, ep12608, em12608, dsL]
  · norm_num [world12608, agent12608, scalar12608, tp12608, tm12608, ep12608, em12608, dsL]
  · norm_num [world12608, agent12608, scalar12608, tp12608, tm12608, ep12608, em12608, dsL]
  · norm_num [world12608, agent12608, scalar12608, tp12608, tm12608, ep12608, em12608, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12608, agent12608, tp12608, tm12608, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12608, agent12608, tp12608, tm12608, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12608, agent12608, scalar12608, tp12608, tm12608, ep12608, em12608, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12608, agent12608, tp12608, tm12608, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12608, agent12608, scalar12608, tp12608, tm12608, ep12608, em12608, dsL]

theorem tails12608 :
    exp (-((12608:ℝ)*ep12608)) ≤ scalar12608.upperTail ∧
    exp (-((12608:ℝ)*em12608)) ≤ scalar12608.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12608:ℝ)) (by norm_num [ep12608]) ?_)
      (show bp12608^8 ≤ scalar12608.upperTail by norm_num [bp12608, scalar12608])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12608, bp12608, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12608:ℝ)) (by norm_num [em12608]) ?_)
      (show bm12608^8 ≤ scalar12608.lowerTail by norm_num [bm12608, scalar12608])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12608, bm12608, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12608 :
    agent12608.root+dsL+scalar12608.worldRadius < √(1/100/aL) ∧
    2*(agent12608.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12608, agent12608, scalar12608, tp12608, tm12608, ep12608, em12608, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12608, agent12608, scalar12608, tp12608, tm12608, ep12608, em12608, dsL]

noncomputable def master12608 : MasterCertificate 12608 world12608 agent12608 :=
  master scalar12608 dsL tp12608 tm12608 ep12608 em12608
    (by norm_num [dsL]) (by norm_num [tp12608]) (by norm_num [tm12608])
    (by norm_num [ep12608]) (by norm_num [em12608])
    positive12608 negative12608 tails12608.1 tails12608.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12608.1 tailGuards12608.2

theorem preserves12608 : master12608.toScalarCertificate = scalar12608 := rfl

noncomputable def tp12609 : ℝ := (1153921343 / 5000000000)
noncomputable def tm12609 : ℝ := (-((3021840307 / 5000000000)))
noncomputable def ep12609 : ℝ := (51166833771988389 / 100000000000000000000)
noncomputable def em12609 : ℝ := (4988491145076903 / 10000000000000000000)
noncomputable def bp12609 : ℝ := (44643866398827607411 / 100000000000000000000)
noncomputable def bm12609 : ℝ := (45555056407094005823 / 100000000000000000000)

theorem positive12609 :
    Eplus aL (agent12609.root+dsL) scalar12609.worldRadius world12609.frame
      agent12609.frame tp12609 ≤ -ep12609 := by
  apply positive_check (eT := (115566700335809960907 / 100000000000000000000)) (y := (18897293716994377801 / 50000000000000000000)) (u := (145928395603079668639 / 100000000000000000000))
  · norm_num [world12609, agent12609, scalar12609, tp12609, tm12609, ep12609, em12609, dsL]
  · norm_num [world12609, agent12609, scalar12609, tp12609, tm12609, ep12609, em12609, dsL]
  · norm_num [world12609, agent12609, scalar12609, tp12609, tm12609, ep12609, em12609, dsL]
  · norm_num [world12609, agent12609, scalar12609, tp12609, tm12609, ep12609, em12609, dsL]
  · norm_num [world12609, agent12609, scalar12609, tp12609, tm12609, ep12609, em12609, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12609, agent12609, tp12609, tm12609, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12609, agent12609, scalar12609, tp12609, tm12609, ep12609, em12609, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12609, agent12609, tp12609, tm12609, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12609, agent12609, scalar12609, tp12609, tm12609, ep12609, em12609, dsL]

theorem negative12609 :
    Eminus aL (agent12609.root+dsL) scalar12609.worldRadius world12609.frame
      agent12609.frame tm12609 ≤ -em12609 := by
  apply negative_check (lo := (68463067359253564557 / 100000000000000000000)) (hi := (34231533679626782279 / 50000000000000000000))
    (y := (-((71698137929269025771 / 100000000000000000000)))) (u := (24411189814640207869 / 50000000000000000000))
  · norm_num [world12609, agent12609, scalar12609, tp12609, tm12609, ep12609, em12609, dsL]
  · norm_num [world12609, agent12609, scalar12609, tp12609, tm12609, ep12609, em12609, dsL]
  · norm_num [world12609, agent12609, scalar12609, tp12609, tm12609, ep12609, em12609, dsL]
  · norm_num [world12609, agent12609, scalar12609, tp12609, tm12609, ep12609, em12609, dsL]
  · norm_num [world12609, agent12609, scalar12609, tp12609, tm12609, ep12609, em12609, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12609, agent12609, tp12609, tm12609, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12609, agent12609, tp12609, tm12609, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12609, agent12609, scalar12609, tp12609, tm12609, ep12609, em12609, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12609, agent12609, tp12609, tm12609, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12609, agent12609, scalar12609, tp12609, tm12609, ep12609, em12609, dsL]

theorem tails12609 :
    exp (-((12609:ℝ)*ep12609)) ≤ scalar12609.upperTail ∧
    exp (-((12609:ℝ)*em12609)) ≤ scalar12609.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12609:ℝ)) (by norm_num [ep12609]) ?_)
      (show bp12609^8 ≤ scalar12609.upperTail by norm_num [bp12609, scalar12609])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12609, bp12609, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12609:ℝ)) (by norm_num [em12609]) ?_)
      (show bm12609^8 ≤ scalar12609.lowerTail by norm_num [bm12609, scalar12609])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12609, bm12609, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12609 :
    agent12609.root+dsL+scalar12609.worldRadius < √(1/100/aL) ∧
    2*(agent12609.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12609, agent12609, scalar12609, tp12609, tm12609, ep12609, em12609, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12609, agent12609, scalar12609, tp12609, tm12609, ep12609, em12609, dsL]

noncomputable def master12609 : MasterCertificate 12609 world12609 agent12609 :=
  master scalar12609 dsL tp12609 tm12609 ep12609 em12609
    (by norm_num [dsL]) (by norm_num [tp12609]) (by norm_num [tm12609])
    (by norm_num [ep12609]) (by norm_num [em12609])
    positive12609 negative12609 tails12609.1 tails12609.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12609.1 tailGuards12609.2

theorem preserves12609 : master12609.toScalarCertificate = scalar12609 := rfl

noncomputable def tp12610 : ℝ := (577001611 / 2500000000)
noncomputable def tm12610 : ℝ := (-((1511024589 / 2500000000)))
noncomputable def ep12610 : ℝ := (5117101159482233 / 10000000000000000000)
noncomputable def em12610 : ℝ := (24944417102581613 / 50000000000000000000)
noncomputable def bp12610 : ℝ := (44638071488828012267 / 100000000000000000000)
noncomputable def bm12610 : ℝ := (45549399341723934397 / 100000000000000000000)

theorem positive12610 :
    Eplus aL (agent12610.root+dsL) scalar12610.worldRadius world12610.frame
      agent12610.frame tp12610 ≤ -ep12610 := by
  apply positive_check (eT := (46227004828955927 / 40000000000000000)) (y := (37794689817560998279 / 100000000000000000000)) (u := (36482136252465121871 / 25000000000000000000))
  · norm_num [world12610, agent12610, scalar12610, tp12610, tm12610, ep12610, em12610, dsL]
  · norm_num [world12610, agent12610, scalar12610, tp12610, tm12610, ep12610, em12610, dsL]
  · norm_num [world12610, agent12610, scalar12610, tp12610, tm12610, ep12610, em12610, dsL]
  · norm_num [world12610, agent12610, scalar12610, tp12610, tm12610, ep12610, em12610, dsL]
  · norm_num [world12610, agent12610, scalar12610, tp12610, tm12610, ep12610, em12610, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12610, agent12610, tp12610, tm12610, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12610, agent12610, scalar12610, tp12610, tm12610, ep12610, em12610, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12610, agent12610, tp12610, tm12610, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12610, agent12610, scalar12610, tp12610, tm12610, ep12610, em12610, dsL]

theorem negative12610 :
    Eminus aL (agent12610.root+dsL) scalar12610.worldRadius world12610.frame
      agent12610.frame tm12610 ≤ -em12610 := by
  apply negative_check (lo := (68461855701751504387 / 100000000000000000000)) (hi := (17115463925437876097 / 25000000000000000000))
    (y := (-((71696331113442880233 / 100000000000000000000)))) (u := (9764652353546308601 / 20000000000000000000))
  · norm_num [world12610, agent12610, scalar12610, tp12610, tm12610, ep12610, em12610, dsL]
  · norm_num [world12610, agent12610, scalar12610, tp12610, tm12610, ep12610, em12610, dsL]
  · norm_num [world12610, agent12610, scalar12610, tp12610, tm12610, ep12610, em12610, dsL]
  · norm_num [world12610, agent12610, scalar12610, tp12610, tm12610, ep12610, em12610, dsL]
  · norm_num [world12610, agent12610, scalar12610, tp12610, tm12610, ep12610, em12610, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12610, agent12610, tp12610, tm12610, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12610, agent12610, tp12610, tm12610, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12610, agent12610, scalar12610, tp12610, tm12610, ep12610, em12610, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12610, agent12610, tp12610, tm12610, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12610, agent12610, scalar12610, tp12610, tm12610, ep12610, em12610, dsL]

theorem tails12610 :
    exp (-((12610:ℝ)*ep12610)) ≤ scalar12610.upperTail ∧
    exp (-((12610:ℝ)*em12610)) ≤ scalar12610.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12610:ℝ)) (by norm_num [ep12610]) ?_)
      (show bp12610^8 ≤ scalar12610.upperTail by norm_num [bp12610, scalar12610])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12610, bp12610, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12610:ℝ)) (by norm_num [em12610]) ?_)
      (show bm12610^8 ≤ scalar12610.lowerTail by norm_num [bm12610, scalar12610])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12610, bm12610, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12610 :
    agent12610.root+dsL+scalar12610.worldRadius < √(1/100/aL) ∧
    2*(agent12610.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12610, agent12610, scalar12610, tp12610, tm12610, ep12610, em12610, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12610, agent12610, scalar12610, tp12610, tm12610, ep12610, em12610, dsL]

noncomputable def master12610 : MasterCertificate 12610 world12610 agent12610 :=
  master scalar12610 dsL tp12610 tm12610 ep12610 em12610
    (by norm_num [dsL]) (by norm_num [tp12610]) (by norm_num [tm12610])
    (by norm_num [ep12610]) (by norm_num [em12610])
    positive12610 negative12610 tails12610.1 tails12610.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12610.1 tailGuards12610.2

theorem preserves12610 : master12610.toScalarCertificate = scalar12610 := rfl

noncomputable def tp12611 : ℝ := (577023751 / 2500000000)
noncomputable def tm12611 : ℝ := (-((6044288869 / 10000000000)))
noncomputable def ep12611 : ℝ := (51173747459347279 / 100000000000000000000)
noncomputable def em12611 : ℝ := (49891187272845647 / 100000000000000000000)
noncomputable def bp12611 : ℝ := (22316645698980681657 / 50000000000000000000)
noncomputable def bm12611 : ℝ := (45544869487300244731 / 100000000000000000000)

theorem positive12611 :
    Eplus aL (agent12611.root+dsL) scalar12611.worldRadius world12611.frame
      agent12611.frame tp12611 ≤ -ep12611 := by
  apply positive_check (eT := (2889194476092092511 / 2500000000000000000)) (y := (1511820810851373469 / 4000000000000000000)) (u := (9120609805245497199 / 6250000000000000000))
  · norm_num [world12611, agent12611, scalar12611, tp12611, tm12611, ep12611, em12611, dsL]
  · norm_num [world12611, agent12611, scalar12611, tp12611, tm12611, ep12611, em12611, dsL]
  · norm_num [world12611, agent12611, scalar12611, tp12611, tm12611, ep12611, em12611, dsL]
  · norm_num [world12611, agent12611, scalar12611, tp12611, tm12611, ep12611, em12611, dsL]
  · norm_num [world12611, agent12611, scalar12611, tp12611, tm12611, ep12611, em12611, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12611, agent12611, tp12611, tm12611, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12611, agent12611, scalar12611, tp12611, tm12611, ep12611, em12611, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12611, agent12611, tp12611, tm12611, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12611, agent12611, scalar12611, tp12611, tm12611, ep12611, em12611, dsL]

theorem negative12611 :
    Eminus aL (agent12611.root+dsL) scalar12611.worldRadius world12611.frame
      agent12611.frame tm12611 ≤ -em12611 := by
  apply negative_check (lo := (68461619229476865773 / 100000000000000000000)) (hi := (34230809614738432887 / 50000000000000000000))
    (y := (-((71696442952927438673 / 100000000000000000000)))) (u := (762862611938715181 / 1562500000000000000))
  · norm_num [world12611, agent12611, scalar12611, tp12611, tm12611, ep12611, em12611, dsL]
  · norm_num [world12611, agent12611, scalar12611, tp12611, tm12611, ep12611, em12611, dsL]
  · norm_num [world12611, agent12611, scalar12611, tp12611, tm12611, ep12611, em12611, dsL]
  · norm_num [world12611, agent12611, scalar12611, tp12611, tm12611, ep12611, em12611, dsL]
  · norm_num [world12611, agent12611, scalar12611, tp12611, tm12611, ep12611, em12611, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12611, agent12611, tp12611, tm12611, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12611, agent12611, tp12611, tm12611, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12611, agent12611, scalar12611, tp12611, tm12611, ep12611, em12611, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12611, agent12611, tp12611, tm12611, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12611, agent12611, scalar12611, tp12611, tm12611, ep12611, em12611, dsL]

theorem tails12611 :
    exp (-((12611:ℝ)*ep12611)) ≤ scalar12611.upperTail ∧
    exp (-((12611:ℝ)*em12611)) ≤ scalar12611.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12611:ℝ)) (by norm_num [ep12611]) ?_)
      (show bp12611^8 ≤ scalar12611.upperTail by norm_num [bp12611, scalar12611])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12611, bp12611, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12611:ℝ)) (by norm_num [em12611]) ?_)
      (show bm12611^8 ≤ scalar12611.lowerTail by norm_num [bm12611, scalar12611])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12611, bm12611, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12611 :
    agent12611.root+dsL+scalar12611.worldRadius < √(1/100/aL) ∧
    2*(agent12611.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12611, agent12611, scalar12611, tp12611, tm12611, ep12611, em12611, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12611, agent12611, scalar12611, tp12611, tm12611, ep12611, em12611, dsL]

noncomputable def master12611 : MasterCertificate 12611 world12611 agent12611 :=
  master scalar12611 dsL tp12611 tm12611 ep12611 em12611
    (by norm_num [dsL]) (by norm_num [tp12611]) (by norm_num [tm12611])
    (by norm_num [ep12611]) (by norm_num [em12611])
    positive12611 negative12611 tails12611.1 tails12611.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12611.1 tailGuards12611.2

theorem preserves12611 : master12611.toScalarCertificate = scalar12611 := rfl

noncomputable def tp12612 : ℝ := (2308183517 / 10000000000)
noncomputable def tm12612 : ℝ := (-((3022239681 / 5000000000)))
noncomputable def ep12612 : ℝ := (51176481546619837 / 100000000000000000000)
noncomputable def em12612 : ℝ := (49893538710672253 / 100000000000000000000)
noncomputable def bp12612 : ℝ := (44628512764148089067 / 100000000000000000000)
noncomputable def bm12612 : ℝ := (22770170492806419951 / 50000000000000000000)

theorem positive12612 :
    Eplus aL (agent12612.root+dsL) scalar12612.worldRadius world12612.frame
      agent12612.frame tp12612 ≤ -ep12612 := by
  apply positive_check (eT := (115568045706991126791 / 100000000000000000000)) (y := (37796350383423257307 / 100000000000000000000)) (u := (145930968269582068689 / 100000000000000000000))
  · norm_num [world12612, agent12612, scalar12612, tp12612, tm12612, ep12612, em12612, dsL]
  · norm_num [world12612, agent12612, scalar12612, tp12612, tm12612, ep12612, em12612, dsL]
  · norm_num [world12612, agent12612, scalar12612, tp12612, tm12612, ep12612, em12612, dsL]
  · norm_num [world12612, agent12612, scalar12612, tp12612, tm12612, ep12612, em12612, dsL]
  · norm_num [world12612, agent12612, scalar12612, tp12612, tm12612, ep12612, em12612, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12612, agent12612, tp12612, tm12612, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12612, agent12612, scalar12612, tp12612, tm12612, ep12612, em12612, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12612, agent12612, tp12612, tm12612, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12612, agent12612, scalar12612, tp12612, tm12612, ep12612, em12612, dsL]

theorem negative12612 :
    Eminus aL (agent12612.root+dsL) scalar12612.worldRadius world12612.frame
      agent12612.frame tm12612 ≤ -em12612 := by
  apply negative_check (lo := (17115345696606332023 / 25000000000000000000)) (hi := (68461382786425328093 / 100000000000000000000))
    (y := (-((71696555475798503699 / 100000000000000000000)))) (u := (24411576113417116513 / 50000000000000000000))
  · norm_num [world12612, agent12612, scalar12612, tp12612, tm12612, ep12612, em12612, dsL]
  · norm_num [world12612, agent12612, scalar12612, tp12612, tm12612, ep12612, em12612, dsL]
  · norm_num [world12612, agent12612, scalar12612, tp12612, tm12612, ep12612, em12612, dsL]
  · norm_num [world12612, agent12612, scalar12612, tp12612, tm12612, ep12612, em12612, dsL]
  · norm_num [world12612, agent12612, scalar12612, tp12612, tm12612, ep12612, em12612, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12612, agent12612, tp12612, tm12612, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12612, agent12612, tp12612, tm12612, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12612, agent12612, scalar12612, tp12612, tm12612, ep12612, em12612, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12612, agent12612, tp12612, tm12612, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12612, agent12612, scalar12612, tp12612, tm12612, ep12612, em12612, dsL]

theorem tails12612 :
    exp (-((12612:ℝ)*ep12612)) ≤ scalar12612.upperTail ∧
    exp (-((12612:ℝ)*em12612)) ≤ scalar12612.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12612:ℝ)) (by norm_num [ep12612]) ?_)
      (show bp12612^8 ≤ scalar12612.upperTail by norm_num [bp12612, scalar12612])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12612, bp12612, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12612:ℝ)) (by norm_num [em12612]) ?_)
      (show bm12612^8 ≤ scalar12612.lowerTail by norm_num [bm12612, scalar12612])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12612, bm12612, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12612 :
    agent12612.root+dsL+scalar12612.worldRadius < √(1/100/aL) ∧
    2*(agent12612.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12612, agent12612, scalar12612, tp12612, tm12612, ep12612, em12612, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12612, agent12612, scalar12612, tp12612, tm12612, ep12612, em12612, dsL]

noncomputable def master12612 : MasterCertificate 12612 world12612 agent12612 :=
  master scalar12612 dsL tp12612 tm12612 ep12612 em12612
    (by norm_num [dsL]) (by norm_num [tp12612]) (by norm_num [tm12612])
    (by norm_num [ep12612]) (by norm_num [em12612])
    positive12612 negative12612 tails12612.1 tails12612.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12612.1 tailGuards12612.2

theorem preserves12612 : master12612.toScalarCertificate = scalar12612 := rfl

noncomputable def tp12613 : ℝ := (144267 / 625000)
noncomputable def tm12613 : ℝ := (-((6044669589 / 10000000000)))
noncomputable def ep12613 : ℝ := (10235842834485527 / 20000000000000000000)
noncomputable def em12613 : ℝ := (49895888788048211 / 100000000000000000000)
noncomputable def bp12613 : ℝ := (44623735365155132481 / 100000000000000000000)
noncomputable def bm12613 : ℝ := (711497088175192409 / 1562500000000000000)

theorem positive12613 :
    Eplus aL (agent12613.root+dsL) scalar12613.worldRadius world12613.frame
      agent12613.frame tp12613 ≤ -ep12613 := by
  apply positive_check (eT := (115568312185439205879 / 100000000000000000000)) (y := (37797180453788214297 / 100000000000000000000)) (u := (72966089802165213853 / 50000000000000000000))
  · norm_num [world12613, agent12613, scalar12613, tp12613, tm12613, ep12613, em12613, dsL]
  · norm_num [world12613, agent12613, scalar12613, tp12613, tm12613, ep12613, em12613, dsL]
  · norm_num [world12613, agent12613, scalar12613, tp12613, tm12613, ep12613, em12613, dsL]
  · norm_num [world12613, agent12613, scalar12613, tp12613, tm12613, ep12613, em12613, dsL]
  · norm_num [world12613, agent12613, scalar12613, tp12613, tm12613, ep12613, em12613, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12613, agent12613, tp12613, tm12613, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12613, agent12613, scalar12613, tp12613, tm12613, ep12613, em12613, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12613, agent12613, tp12613, tm12613, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12613, agent12613, scalar12613, tp12613, tm12613, ep12613, em12613, dsL]

theorem negative12613 :
    Eminus aL (agent12613.root+dsL) scalar12613.worldRadius world12613.frame
      agent12613.frame tm12613 ≤ -em12613 := by
  apply negative_check (lo := (68461147428352888079 / 100000000000000000000)) (hi := (855764342854411101 / 1250000000000000000))
    (y := (-((35848333142544775249 / 50000000000000000000)))) (u := (24411549063137679 / 50000000000000000))
  · norm_num [world12613, agent12613, scalar12613, tp12613, tm12613, ep12613, em12613, dsL]
  · norm_num [world12613, agent12613, scalar12613, tp12613, tm12613, ep12613, em12613, dsL]
  · norm_num [world12613, agent12613, scalar12613, tp12613, tm12613, ep12613, em12613, dsL]
  · norm_num [world12613, agent12613, scalar12613, tp12613, tm12613, ep12613, em12613, dsL]
  · norm_num [world12613, agent12613, scalar12613, tp12613, tm12613, ep12613, em12613, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12613, agent12613, tp12613, tm12613, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12613, agent12613, tp12613, tm12613, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12613, agent12613, scalar12613, tp12613, tm12613, ep12613, em12613, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12613, agent12613, tp12613, tm12613, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12613, agent12613, scalar12613, tp12613, tm12613, ep12613, em12613, dsL]

theorem tails12613 :
    exp (-((12613:ℝ)*ep12613)) ≤ scalar12613.upperTail ∧
    exp (-((12613:ℝ)*em12613)) ≤ scalar12613.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12613:ℝ)) (by norm_num [ep12613]) ?_)
      (show bp12613^8 ≤ scalar12613.upperTail by norm_num [bp12613, scalar12613])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12613, bp12613, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12613:ℝ)) (by norm_num [em12613]) ?_)
      (show bm12613^8 ≤ scalar12613.lowerTail by norm_num [bm12613, scalar12613])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12613, bm12613, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12613 :
    agent12613.root+dsL+scalar12613.worldRadius < √(1/100/aL) ∧
    2*(agent12613.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12613, agent12613, scalar12613, tp12613, tm12613, ep12613, em12613, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12613, agent12613, scalar12613, tp12613, tm12613, ep12613, em12613, dsL]

noncomputable def master12613 : MasterCertificate 12613 world12613 agent12613 :=
  master scalar12613 dsL tp12613 tm12613 ep12613 em12613
    (by norm_num [dsL]) (by norm_num [tp12613]) (by norm_num [tm12613])
    (by norm_num [ep12613]) (by norm_num [em12613])
    positive12613 negative12613 tails12613.1 tails12613.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12613.1 tailGuards12613.2

theorem preserves12613 : master12613.toScalarCertificate = scalar12613 := rfl

noncomputable def tp12614 : ℝ := (577090099 / 2500000000)
noncomputable def tm12614 : ℝ := (-((1511214919 / 2500000000)))
noncomputable def ep12614 : ℝ := (51181945794054163 / 100000000000000000000)
noncomputable def em12614 : ℝ := (4989823792227403 / 10000000000000000000)
noncomputable def bp12614 : ℝ := (44618958879227603609 / 100000000000000000000)
noncomputable def bm12614 : ℝ := (11382821790122152073 / 25000000000000000000)

theorem positive12614 :
    Eplus aL (agent12614.root+dsL) scalar12614.worldRadius world12614.frame
      agent12614.frame tp12614 ≤ -ep12614 := by
  apply positive_check (eT := (1805759032284156023 / 1562500000000000000)) (y := (37798009328965701931 / 100000000000000000000)) (u := (72966694602478083707 / 50000000000000000000))
  · norm_num [world12614, agent12614, scalar12614, tp12614, tm12614, ep12614, em12614, dsL]
  · norm_num [world12614, agent12614, scalar12614, tp12614, tm12614, ep12614, em12614, dsL]
  · norm_num [world12614, agent12614, scalar12614, tp12614, tm12614, ep12614, em12614, dsL]
  · norm_num [world12614, agent12614, scalar12614, tp12614, tm12614, ep12614, em12614, dsL]
  · norm_num [world12614, agent12614, scalar12614, tp12614, tm12614, ep12614, em12614, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12614, agent12614, tp12614, tm12614, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12614, agent12614, scalar12614, tp12614, tm12614, ep12614, em12614, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12614, agent12614, tp12614, tm12614, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12614, agent12614, scalar12614, tp12614, tm12614, ep12614, em12614, dsL]

theorem negative12614 :
    Eminus aL (agent12614.root+dsL) scalar12614.worldRadius world12614.frame
      agent12614.frame tm12614 ≤ -em12614 := by
  apply negative_check (lo := (17115228153593908843 / 25000000000000000000)) (hi := (68460912614375635373 / 100000000000000000000))
    (y := (-((14339355265038686607 / 20000000000000000000)))) (u := (48823044401317020679 / 100000000000000000000))
  · norm_num [world12614, agent12614, scalar12614, tp12614, tm12614, ep12614, em12614, dsL]
  · norm_num [world12614, agent12614, scalar12614, tp12614, tm12614, ep12614, em12614, dsL]
  · norm_num [world12614, agent12614, scalar12614, tp12614, tm12614, ep12614, em12614, dsL]
  · norm_num [world12614, agent12614, scalar12614, tp12614, tm12614, ep12614, em12614, dsL]
  · norm_num [world12614, agent12614, scalar12614, tp12614, tm12614, ep12614, em12614, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12614, agent12614, tp12614, tm12614, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12614, agent12614, tp12614, tm12614, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12614, agent12614, scalar12614, tp12614, tm12614, ep12614, em12614, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12614, agent12614, tp12614, tm12614, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12614, agent12614, scalar12614, tp12614, tm12614, ep12614, em12614, dsL]

theorem tails12614 :
    exp (-((12614:ℝ)*ep12614)) ≤ scalar12614.upperTail ∧
    exp (-((12614:ℝ)*em12614)) ≤ scalar12614.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12614:ℝ)) (by norm_num [ep12614]) ?_)
      (show bp12614^8 ≤ scalar12614.upperTail by norm_num [bp12614, scalar12614])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12614, bp12614, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12614:ℝ)) (by norm_num [em12614]) ?_)
      (show bm12614^8 ≤ scalar12614.lowerTail by norm_num [bm12614, scalar12614])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12614, bm12614, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12614 :
    agent12614.root+dsL+scalar12614.worldRadius < √(1/100/aL) ∧
    2*(agent12614.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12614, agent12614, scalar12614, tp12614, tm12614, ep12614, em12614, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12614, agent12614, scalar12614, tp12614, tm12614, ep12614, em12614, dsL]

noncomputable def master12614 : MasterCertificate 12614 world12614 agent12614 :=
  master scalar12614 dsL tp12614 tm12614 ep12614 em12614
    (by norm_num [dsL]) (by norm_num [tp12614]) (by norm_num [tm12614])
    (by norm_num [ep12614]) (by norm_num [em12614])
    positive12614 negative12614 tails12614.1 tails12614.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12614.1 tailGuards12614.2

theorem preserves12614 : master12614.toScalarCertificate = scalar12614 := rfl

noncomputable def tp12615 : ℝ := (461689751 / 2000000000)
noncomputable def tm12615 : ℝ := (-((1209009971 / 2000000000)))
noncomputable def ep12615 : ℝ := (25592337819256713 / 50000000000000000000)
noncomputable def em12615 : ℝ := (24950292713430357 / 50000000000000000000)
noncomputable def bp12615 : ℝ := (8922836770030617437 / 20000000000000000000)
noncomputable def bm12615 : ℝ := (9105352406053277201 / 20000000000000000000)

theorem positive12615 :
    Eplus aL (agent12615.root+dsL) scalar12615.worldRadius world12615.frame
      agent12615.frame tp12615 ≤ -ep12615 := by
  apply positive_check (eT := (115568843711395994133 / 100000000000000000000)) (y := (3779883803794927069 / 10000000000000000000)) (u := (145934598573073599443 / 100000000000000000000))
  · norm_num [world12615, agent12615, scalar12615, tp12615, tm12615, ep12615, em12615, dsL]
  · norm_num [world12615, agent12615, scalar12615, tp12615, tm12615, ep12615, em12615, dsL]
  · norm_num [world12615, agent12615, scalar12615, tp12615, tm12615, ep12615, em12615, dsL]
  · norm_num [world12615, agent12615, scalar12615, tp12615, tm12615, ep12615, em12615, dsL]
  · norm_num [world12615, agent12615, scalar12615, tp12615, tm12615, ep12615, em12615, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12615, agent12615, tp12615, tm12615, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12615, agent12615, scalar12615, tp12615, tm12615, ep12615, em12615, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12615, agent12615, tp12615, tm12615, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12615, agent12615, scalar12615, tp12615, tm12615, ep12615, em12615, dsL]

theorem negative12615 :
    Eminus aL (agent12615.root+dsL) scalar12615.worldRadius world12615.frame
      agent12615.frame tm12615 ≤ -em12615 := by
  apply negative_check (lo := (68460677349005929579 / 100000000000000000000)) (hi := (3423033867450296479 / 5000000000000000000))
    (y := (-((17924222035066411313 / 25000000000000000000)))) (u := (48822989809825187907 / 100000000000000000000))
  · norm_num [world12615, agent12615, scalar12615, tp12615, tm12615, ep12615, em12615, dsL]
  · norm_num [world12615, agent12615, scalar12615, tp12615, tm12615, ep12615, em12615, dsL]
  · norm_num [world12615, agent12615, scalar12615, tp12615, tm12615, ep12615, em12615, dsL]
  · norm_num [world12615, agent12615, scalar12615, tp12615, tm12615, ep12615, em12615, dsL]
  · norm_num [world12615, agent12615, scalar12615, tp12615, tm12615, ep12615, em12615, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12615, agent12615, tp12615, tm12615, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12615, agent12615, tp12615, tm12615, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12615, agent12615, scalar12615, tp12615, tm12615, ep12615, em12615, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12615, agent12615, tp12615, tm12615, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12615, agent12615, scalar12615, tp12615, tm12615, ep12615, em12615, dsL]

theorem tails12615 :
    exp (-((12615:ℝ)*ep12615)) ≤ scalar12615.upperTail ∧
    exp (-((12615:ℝ)*em12615)) ≤ scalar12615.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12615:ℝ)) (by norm_num [ep12615]) ?_)
      (show bp12615^8 ≤ scalar12615.upperTail by norm_num [bp12615, scalar12615])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12615, bp12615, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12615:ℝ)) (by norm_num [em12615]) ?_)
      (show bm12615^8 ≤ scalar12615.lowerTail by norm_num [bm12615, scalar12615])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12615, bm12615, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12615 :
    agent12615.root+dsL+scalar12615.worldRadius < √(1/100/aL) ∧
    2*(agent12615.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12615, agent12615, scalar12615, tp12615, tm12615, ep12615, em12615, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12615, agent12615, scalar12615, tp12615, tm12615, ep12615, em12615, dsL]

noncomputable def master12615 : MasterCertificate 12615 world12615 agent12615 :=
  master scalar12615 dsL tp12615 tm12615 ep12615 em12615
    (by norm_num [dsL]) (by norm_num [tp12615]) (by norm_num [tm12615])
    (by norm_num [ep12615]) (by norm_num [em12615])
    positive12615 negative12615 tails12615.1 tails12615.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12615.1 tailGuards12615.2

theorem preserves12615 : master12615.toScalarCertificate = scalar12615 := rfl

noncomputable def tp12616 : ℝ := (1154268559 / 5000000000)
noncomputable def tm12616 : ℝ := (-((755654959 / 1250000000)))
noncomputable def ep12616 : ℝ := (51187404483603713 / 100000000000000000000)
noncomputable def em12616 : ℝ := (12475732998124267 / 25000000000000000000)
noncomputable def bp12616 : ℝ := (44609409730696942251 / 100000000000000000000)
noncomputable def bm12616 : ℝ := (1820889510266976079 / 4000000000000000000)

theorem positive12616 :
    Eplus aL (agent12616.root+dsL) scalar12616.worldRadius world12616.frame
      agent12616.frame tp12616 ≤ -ep12616 := by
  apply positive_check (eT := (28892277354522522983 / 25000000000000000000)) (y := (1511986686074341457 / 4000000000000000000)) (u := (145935808542144803913 / 100000000000000000000))
  · norm_num [world12616, agent12616, scalar12616, tp12616, tm12616, ep12616, em12616, dsL]
  · norm_num [world12616, agent12616, scalar12616, tp12616, tm12616, ep12616, em12616, dsL]
  · norm_num [world12616, agent12616, scalar12616, tp12616, tm12616, ep12616, em12616, dsL]
  · norm_num [world12616, agent12616, scalar12616, tp12616, tm12616, ep12616, em12616, dsL]
  · norm_num [world12616, agent12616, scalar12616, tp12616, tm12616, ep12616, em12616, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12616, agent12616, tp12616, tm12616, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12616, agent12616, scalar12616, tp12616, tm12616, ep12616, em12616, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12616, agent12616, tp12616, tm12616, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12616, agent12616, scalar12616, tp12616, tm12616, ep12616, em12616, dsL]

theorem negative12616 :
    Eminus aL (agent12616.root+dsL) scalar12616.worldRadius world12616.frame
      agent12616.frame tm12616 ≤ -em12616 := by
  apply negative_check (lo := (17115110895104441193 / 25000000000000000000)) (hi := (68460443580417764773 / 100000000000000000000))
    (y := (-((71696997019928082273 / 100000000000000000000)))) (u := (4882293665154763059 / 10000000000000000000))
  · norm_num [world12616, agent12616, scalar12616, tp12616, tm12616, ep12616, em12616, dsL]
  · norm_num [world12616, agent12616, scalar12616, tp12616, tm12616, ep12616, em12616, dsL]
  · norm_num [world12616, agent12616, scalar12616, tp12616, tm12616, ep12616, em12616, dsL]
  · norm_num [world12616, agent12616, scalar12616, tp12616, tm12616, ep12616, em12616, dsL]
  · norm_num [world12616, agent12616, scalar12616, tp12616, tm12616, ep12616, em12616, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12616, agent12616, tp12616, tm12616, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12616, agent12616, tp12616, tm12616, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12616, agent12616, scalar12616, tp12616, tm12616, ep12616, em12616, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12616, agent12616, tp12616, tm12616, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12616, agent12616, scalar12616, tp12616, tm12616, ep12616, em12616, dsL]

theorem tails12616 :
    exp (-((12616:ℝ)*ep12616)) ≤ scalar12616.upperTail ∧
    exp (-((12616:ℝ)*em12616)) ≤ scalar12616.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12616:ℝ)) (by norm_num [ep12616]) ?_)
      (show bp12616^8 ≤ scalar12616.upperTail by norm_num [bp12616, scalar12616])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12616, bp12616, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12616:ℝ)) (by norm_num [em12616]) ?_)
      (show bm12616^8 ≤ scalar12616.lowerTail by norm_num [bm12616, scalar12616])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12616, bm12616, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12616 :
    agent12616.root+dsL+scalar12616.worldRadius < √(1/100/aL) ∧
    2*(agent12616.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12616, agent12616, scalar12616, tp12616, tm12616, ep12616, em12616, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12616, agent12616, scalar12616, tp12616, tm12616, ep12616, em12616, dsL]

noncomputable def master12616 : MasterCertificate 12616 world12616 agent12616 :=
  master scalar12616 dsL tp12616 tm12616 ep12616 em12616
    (by norm_num [dsL]) (by norm_num [tp12616]) (by norm_num [tm12616])
    (by norm_num [ep12616]) (by norm_num [em12616])
    positive12616 negative12616 tails12616.1 tails12616.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12616.1 tailGuards12616.2

theorem preserves12616 : master12616.toScalarCertificate = scalar12616 := rfl

noncomputable def tp12617 : ℝ := (115431269 / 500000000)
noncomputable def tm12617 : ℝ := (-((3022714777 / 5000000000)))
noncomputable def ep12617 : ℝ := (25595065942390889 / 50000000000000000000)
noncomputable def em12617 : ℝ := (49905277219602477 / 100000000000000000000)
noncomputable def bp12617 : ℝ := (2787789802097931683 / 6250000000000000000)
noncomputable def bm12617 : ℝ := (45517714626554359471 / 100000000000000000000)

theorem positive12617 :
    Eplus aL (agent12617.root+dsL) scalar12617.worldRadius world12617.frame
      agent12617.frame tp12617 ≤ -ep12617 := by
  apply positive_check (eT := (57784687212842780359 / 50000000000000000000)) (y := (9450123769098458727 / 25000000000000000000)) (u := (72968508392755587643 / 50000000000000000000))
  · norm_num [world12617, agent12617, scalar12617, tp12617, tm12617, ep12617, em12617, dsL]
  · norm_num [world12617, agent12617, scalar12617, tp12617, tm12617, ep12617, em12617, dsL]
  · norm_num [world12617, agent12617, scalar12617, tp12617, tm12617, ep12617, em12617, dsL]
  · norm_num [world12617, agent12617, scalar12617, tp12617, tm12617, ep12617, em12617, dsL]
  · norm_num [world12617, agent12617, scalar12617, tp12617, tm12617, ep12617, em12617, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12617, agent12617, tp12617, tm12617, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12617, agent12617, scalar12617, tp12617, tm12617, ep12617, em12617, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12617, agent12617, tp12617, tm12617, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12617, agent12617, scalar12617, tp12617, tm12617, ep12617, em12617, dsL]

theorem negative12617 :
    Eminus aL (agent12617.root+dsL) scalar12617.worldRadius world12617.frame
      agent12617.frame tm12617 ≤ -em12617 := by
  apply negative_check (lo := (106969077306620971 / 156250000000000000)) (hi := (68460209476237421441 / 100000000000000000000))
    (y := (-((71697107826221931459 / 100000000000000000000)))) (u := (48822882552690951149 / 100000000000000000000))
  · norm_num [world12617, agent12617, scalar12617, tp12617, tm12617, ep12617, em12617, dsL]
  · norm_num [world12617, agent12617, scalar12617, tp12617, tm12617, ep12617, em12617, dsL]
  · norm_num [world12617, agent12617, scalar12617, tp12617, tm12617, ep12617, em12617, dsL]
  · norm_num [world12617, agent12617, scalar12617, tp12617, tm12617, ep12617, em12617, dsL]
  · norm_num [world12617, agent12617, scalar12617, tp12617, tm12617, ep12617, em12617, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12617, agent12617, tp12617, tm12617, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12617, agent12617, tp12617, tm12617, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12617, agent12617, scalar12617, tp12617, tm12617, ep12617, em12617, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12617, agent12617, tp12617, tm12617, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12617, agent12617, scalar12617, tp12617, tm12617, ep12617, em12617, dsL]

theorem tails12617 :
    exp (-((12617:ℝ)*ep12617)) ≤ scalar12617.upperTail ∧
    exp (-((12617:ℝ)*em12617)) ≤ scalar12617.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12617:ℝ)) (by norm_num [ep12617]) ?_)
      (show bp12617^8 ≤ scalar12617.upperTail by norm_num [bp12617, scalar12617])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12617, bp12617, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12617:ℝ)) (by norm_num [em12617]) ?_)
      (show bm12617^8 ≤ scalar12617.lowerTail by norm_num [bm12617, scalar12617])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12617, bm12617, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12617 :
    agent12617.root+dsL+scalar12617.worldRadius < √(1/100/aL) ∧
    2*(agent12617.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12617, agent12617, scalar12617, tp12617, tm12617, ep12617, em12617, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12617, agent12617, scalar12617, tp12617, tm12617, ep12617, em12617, dsL]

noncomputable def master12617 : MasterCertificate 12617 world12617 agent12617 :=
  master scalar12617 dsL tp12617 tm12617 ep12617 em12617
    (by norm_num [dsL]) (by norm_num [tp12617]) (by norm_num [tm12617])
    (by norm_num [ep12617]) (by norm_num [em12617])
    positive12617 negative12617 tails12617.1 tails12617.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12617.1 tailGuards12617.2

theorem preserves12617 : master12617.toScalarCertificate = scalar12617 := rfl

noncomputable def tp12618 : ℝ := (2308713583 / 10000000000)
noncomputable def tm12618 : ℝ := (-((3022809621 / 5000000000)))
noncomputable def ep12618 : ℝ := (5119285701342019 / 10000000000000000000)
noncomputable def em12618 : ℝ := (2495381017362957 / 5000000000000000000)
noncomputable def bp12618 : ℝ := (557498321770256917 / 1250000000000000000)
noncomputable def bm12618 : ℝ := (22756596593056623143 / 50000000000000000000)

theorem positive12618 :
    Eplus aL (agent12618.root+dsL) scalar12618.worldRadius world12618.frame
      agent12618.frame tp12618 ≤ -ep12618 := by
  apply positive_check (eT := (57784819519218065249 / 50000000000000000000)) (y := (37801322292513674407 / 100000000000000000000)) (u := (29187644801006397653 / 20000000000000000000))
  · norm_num [world12618, agent12618, scalar12618, tp12618, tm12618, ep12618, em12618, dsL]
  · norm_num [world12618, agent12618, scalar12618, tp12618, tm12618, ep12618, em12618, dsL]
  · norm_num [world12618, agent12618, scalar12618, tp12618, tm12618, ep12618, em12618, dsL]
  · norm_num [world12618, agent12618, scalar12618, tp12618, tm12618, ep12618, em12618, dsL]
  · norm_num [world12618, agent12618, scalar12618, tp12618, tm12618, ep12618, em12618, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12618, agent12618, tp12618, tm12618, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12618, agent12618, scalar12618, tp12618, tm12618, ep12618, em12618, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12618, agent12618, tp12618, tm12618, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12618, agent12618, scalar12618, tp12618, tm12618, ep12618, em12618, dsL]

theorem negative12618 :
    Eminus aL (agent12618.root+dsL) scalar12618.worldRadius world12618.frame
      agent12618.frame tm12618 ≤ -em12618 := by
  apply negative_check (lo := (68459976147852777151 / 100000000000000000000)) (hi := (1069687127310199643 / 1562500000000000000))
    (y := (-((17924304165753576597 / 25000000000000000000)))) (u := (9764565883092110451 / 20000000000000000000))
  · norm_num [world12618, agent12618, scalar12618, tp12618, tm12618, ep12618, em12618, dsL]
  · norm_num [world12618, agent12618, scalar12618, tp12618, tm12618, ep12618, em12618, dsL]
  · norm_num [world12618, agent12618, scalar12618, tp12618, tm12618, ep12618, em12618, dsL]
  · norm_num [world12618, agent12618, scalar12618, tp12618, tm12618, ep12618, em12618, dsL]
  · norm_num [world12618, agent12618, scalar12618, tp12618, tm12618, ep12618, em12618, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12618, agent12618, tp12618, tm12618, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12618, agent12618, tp12618, tm12618, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12618, agent12618, scalar12618, tp12618, tm12618, ep12618, em12618, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12618, agent12618, tp12618, tm12618, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12618, agent12618, scalar12618, tp12618, tm12618, ep12618, em12618, dsL]

theorem tails12618 :
    exp (-((12618:ℝ)*ep12618)) ≤ scalar12618.upperTail ∧
    exp (-((12618:ℝ)*em12618)) ≤ scalar12618.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12618:ℝ)) (by norm_num [ep12618]) ?_)
      (show bp12618^8 ≤ scalar12618.upperTail by norm_num [bp12618, scalar12618])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12618, bp12618, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12618:ℝ)) (by norm_num [em12618]) ?_)
      (show bm12618^8 ≤ scalar12618.lowerTail by norm_num [bm12618, scalar12618])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12618, bm12618, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12618 :
    agent12618.root+dsL+scalar12618.worldRadius < √(1/100/aL) ∧
    2*(agent12618.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12618, agent12618, scalar12618, tp12618, tm12618, ep12618, em12618, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12618, agent12618, scalar12618, tp12618, tm12618, ep12618, em12618, dsL]

noncomputable def master12618 : MasterCertificate 12618 world12618 agent12618 :=
  master scalar12618 dsL tp12618 tm12618 ep12618 em12618
    (by norm_num [dsL]) (by norm_num [tp12618]) (by norm_num [tm12618])
    (by norm_num [ep12618]) (by norm_num [em12618])
    positive12618 negative12618 tails12618.1 tails12618.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12618.1 tailGuards12618.2

theorem preserves12618 : master12618.toScalarCertificate = scalar12618 := rfl

noncomputable def tp12619 : ℝ := (92352073 / 400000000)
noncomputable def tm12619 : ℝ := (-((604580899 / 1000000000)))
noncomputable def ep12619 : ℝ := (51195581638310927 / 100000000000000000000)
noncomputable def em12619 : ℝ := (3119372687893139 / 6250000000000000000)
noncomputable def bp12619 : ℝ := (11148773802635798691 / 25000000000000000000)
noncomputable def bm12619 : ℝ := (4550867226462103407 / 10000000000000000000)

theorem positive12619 :
    Eplus aL (agent12619.root+dsL) scalar12619.worldRadius world12619.frame
      agent12619.frame tp12619 ≤ -ep12619 := by
  apply positive_check (eT := (7223118997887611489 / 6250000000000000000)) (y := (18901075341644344983 / 50000000000000000000)) (u := (36484858237206062501 / 25000000000000000000))
  · norm_num [world12619, agent12619, scalar12619, tp12619, tm12619, ep12619, em12619, dsL]
  · norm_num [world12619, agent12619, scalar12619, tp12619, tm12619, ep12619, em12619, dsL]
  · norm_num [world12619, agent12619, scalar12619, tp12619, tm12619, ep12619, em12619, dsL]
  · norm_num [world12619, agent12619, scalar12619, tp12619, tm12619, ep12619, em12619, dsL]
  · norm_num [world12619, agent12619, scalar12619, tp12619, tm12619, ep12619, em12619, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12619, agent12619, tp12619, tm12619, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12619, agent12619, scalar12619, tp12619, tm12619, ep12619, em12619, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12619, agent12619, tp12619, tm12619, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12619, agent12619, scalar12619, tp12619, tm12619, ep12619, em12619, dsL]

theorem negative12619 :
    Eminus aL (agent12619.root+dsL) scalar12619.worldRadius world12619.frame
      agent12619.frame tm12619 ≤ -em12619 := by
  apply negative_check (lo := (1069683476646590587 / 1562500000000000000)) (hi := (68459742505381797569 / 100000000000000000000))
    (y := (-((8962165954154757077 / 12500000000000000000)))) (u := (9764555047337513977 / 20000000000000000000))
  · norm_num [world12619, agent12619, scalar12619, tp12619, tm12619, ep12619, em12619, dsL]
  · norm_num [world12619, agent12619, scalar12619, tp12619, tm12619, ep12619, em12619, dsL]
  · norm_num [world12619, agent12619, scalar12619, tp12619, tm12619, ep12619, em12619, dsL]
  · norm_num [world12619, agent12619, scalar12619, tp12619, tm12619, ep12619, em12619, dsL]
  · norm_num [world12619, agent12619, scalar12619, tp12619, tm12619, ep12619, em12619, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12619, agent12619, tp12619, tm12619, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12619, agent12619, tp12619, tm12619, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12619, agent12619, scalar12619, tp12619, tm12619, ep12619, em12619, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12619, agent12619, tp12619, tm12619, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12619, agent12619, scalar12619, tp12619, tm12619, ep12619, em12619, dsL]

theorem tails12619 :
    exp (-((12619:ℝ)*ep12619)) ≤ scalar12619.upperTail ∧
    exp (-((12619:ℝ)*em12619)) ≤ scalar12619.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12619:ℝ)) (by norm_num [ep12619]) ?_)
      (show bp12619^8 ≤ scalar12619.upperTail by norm_num [bp12619, scalar12619])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12619, bp12619, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12619:ℝ)) (by norm_num [em12619]) ?_)
      (show bm12619^8 ≤ scalar12619.lowerTail by norm_num [bm12619, scalar12619])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12619, bm12619, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12619 :
    agent12619.root+dsL+scalar12619.worldRadius < √(1/100/aL) ∧
    2*(agent12619.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12619, agent12619, scalar12619, tp12619, tm12619, ep12619, em12619, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12619, agent12619, scalar12619, tp12619, tm12619, ep12619, em12619, dsL]

noncomputable def master12619 : MasterCertificate 12619 world12619 agent12619 :=
  master scalar12619 dsL tp12619 tm12619 ep12619 em12619
    (by norm_num [dsL]) (by norm_num [tp12619]) (by norm_num [tm12619])
    (by norm_num [ep12619]) (by norm_num [em12619])
    positive12619 negative12619 tails12619.1 tails12619.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12619.1 tailGuards12619.2

theorem preserves12619 : master12619.toScalarCertificate = scalar12619 := rfl

noncomputable def tp12620 : ℝ := (2308965091 / 10000000000)
noncomputable def tm12620 : ℝ := (-((1209245093 / 2000000000)))
noncomputable def ep12620 : ℝ := (51199743924914503 / 100000000000000000000)
noncomputable def em12620 : ℝ := (24956935551664841 / 50000000000000000000)
noncomputable def bp12620 : ℝ := (22294656814216591263 / 50000000000000000000)
noncomputable def bm12620 : ℝ := (22751513912177515653 / 50000000000000000000)

theorem positive12620 :
    Eplus aL (agent12620.root+dsL) scalar12620.worldRadius world12620.frame
      agent12620.frame tp12620 ≤ -ep12620 := by
  apply positive_check (eT := (115570712346136660579 / 100000000000000000000)) (y := (18901125214229374307 / 50000000000000000000)) (u := (18242447314554053219 / 12500000000000000000))
  · norm_num [world12620, agent12620, scalar12620, tp12620, tm12620, ep12620, em12620, dsL]
  · norm_num [world12620, agent12620, scalar12620, tp12620, tm12620, ep12620, em12620, dsL]
  · norm_num [world12620, agent12620, scalar12620, tp12620, tm12620, ep12620, em12620, dsL]
  · norm_num [world12620, agent12620, scalar12620, tp12620, tm12620, ep12620, em12620, dsL]
  · norm_num [world12620, agent12620, scalar12620, tp12620, tm12620, ep12620, em12620, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12620, agent12620, tp12620, tm12620, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12620, agent12620, scalar12620, tp12620, tm12620, ep12620, em12620, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12620, agent12620, tp12620, tm12620, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12620, agent12620, scalar12620, tp12620, tm12620, ep12620, em12620, dsL]

theorem negative12620 :
    Eminus aL (agent12620.root+dsL) scalar12620.worldRadius world12620.frame
      agent12620.frame tm12620 ≤ -em12620 := by
  apply negative_check (lo := (17114634002282768769 / 25000000000000000000)) (hi := (68458536009131075077 / 100000000000000000000))
    (y := (-((7169551976470543969 / 10000000000000000000)))) (u := (24411828948128231253 / 50000000000000000000))
  · norm_num [world12620, agent12620, scalar12620, tp12620, tm12620, ep12620, em12620, dsL]
  · norm_num [world12620, agent12620, scalar12620, tp12620, tm12620, ep12620, em12620, dsL]
  · norm_num [world12620, agent12620, scalar12620, tp12620, tm12620, ep12620, em12620, dsL]
  · norm_num [world12620, agent12620, scalar12620, tp12620, tm12620, ep12620, em12620, dsL]
  · norm_num [world12620, agent12620, scalar12620, tp12620, tm12620, ep12620, em12620, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12620, agent12620, tp12620, tm12620, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12620, agent12620, tp12620, tm12620, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12620, agent12620, scalar12620, tp12620, tm12620, ep12620, em12620, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12620, agent12620, tp12620, tm12620, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12620, agent12620, scalar12620, tp12620, tm12620, ep12620, em12620, dsL]

theorem tails12620 :
    exp (-((12620:ℝ)*ep12620)) ≤ scalar12620.upperTail ∧
    exp (-((12620:ℝ)*em12620)) ≤ scalar12620.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12620:ℝ)) (by norm_num [ep12620]) ?_)
      (show bp12620^8 ≤ scalar12620.upperTail by norm_num [bp12620, scalar12620])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12620, bp12620, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12620:ℝ)) (by norm_num [em12620]) ?_)
      (show bm12620^8 ≤ scalar12620.lowerTail by norm_num [bm12620, scalar12620])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12620, bm12620, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12620 :
    agent12620.root+dsL+scalar12620.worldRadius < √(1/100/aL) ∧
    2*(agent12620.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12620, agent12620, scalar12620, tp12620, tm12620, ep12620, em12620, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12620, agent12620, scalar12620, tp12620, tm12620, ep12620, em12620, dsL]

noncomputable def master12620 : MasterCertificate 12620 world12620 agent12620 :=
  master scalar12620 dsL tp12620 tm12620 ep12620 em12620
    (by norm_num [dsL]) (by norm_num [tp12620]) (by norm_num [tm12620])
    (by norm_num [ep12620]) (by norm_num [em12620])
    positive12620 negative12620 tails12620.1 tails12620.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12620.1 tailGuards12620.2

theorem preserves12620 : master12620.toScalarCertificate = scalar12620 := rfl

noncomputable def tp12621 : ℝ := (2309053203 / 10000000000)
noncomputable def tm12621 : ℝ := (-((1511603733 / 2500000000)))
noncomputable def ep12621 : ℝ := (51202465554173889 / 100000000000000000000)
noncomputable def em12621 : ℝ := (24958105506471239 / 50000000000000000000)
noncomputable def bp12621 : ℝ := (44584545645595778073 / 100000000000000000000)
noncomputable def bm12621 : ℝ := (45498509264161844827 / 100000000000000000000)

theorem positive12621 :
    Eplus aL (agent12621.root+dsL) scalar12621.worldRadius world12621.frame
      agent12621.frame tp12621 ≤ -ep12621 := by
  apply positive_check (eT := (115570976386397987127 / 100000000000000000000)) (y := (2362692322559925937 / 6250000000000000000)) (u := (36485196262836470561 / 25000000000000000000))
  · norm_num [world12621, agent12621, scalar12621, tp12621, tm12621, ep12621, em12621, dsL]
  · norm_num [world12621, agent12621, scalar12621, tp12621, tm12621, ep12621, em12621, dsL]
  · norm_num [world12621, agent12621, scalar12621, tp12621, tm12621, ep12621, em12621, dsL]
  · norm_num [world12621, agent12621, scalar12621, tp12621, tm12621, ep12621, em12621, dsL]
  · norm_num [world12621, agent12621, scalar12621, tp12621, tm12621, ep12621, em12621, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12621, agent12621, tp12621, tm12621, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12621, agent12621, scalar12621, tp12621, tm12621, ep12621, em12621, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12621, agent12621, tp12621, tm12621, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12621, agent12621, scalar12621, tp12621, tm12621, ep12621, em12621, dsL]

theorem negative12621 :
    Eminus aL (agent12621.root+dsL) scalar12621.worldRadius world12621.frame
      agent12621.frame tm12621 ≤ -em12621 := by
  apply negative_check (lo := (342291517420638153 / 500000000000000000)) (hi := (68458303484127630601 / 100000000000000000000))
    (y := (-((17923907232718034833 / 25000000000000000000)))) (u := (48823604597369786797 / 100000000000000000000))
  · norm_num [world12621, agent12621, scalar12621, tp12621, tm12621, ep12621, em12621, dsL]
  · norm_num [world12621, agent12621, scalar12621, tp12621, tm12621, ep12621, em12621, dsL]
  · norm_num [world12621, agent12621, scalar12621, tp12621, tm12621, ep12621, em12621, dsL]
  · norm_num [world12621, agent12621, scalar12621, tp12621, tm12621, ep12621, em12621, dsL]
  · norm_num [world12621, agent12621, scalar12621, tp12621, tm12621, ep12621, em12621, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12621, agent12621, tp12621, tm12621, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12621, agent12621, tp12621, tm12621, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12621, agent12621, scalar12621, tp12621, tm12621, ep12621, em12621, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12621, agent12621, tp12621, tm12621, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12621, agent12621, scalar12621, tp12621, tm12621, ep12621, em12621, dsL]

theorem tails12621 :
    exp (-((12621:ℝ)*ep12621)) ≤ scalar12621.upperTail ∧
    exp (-((12621:ℝ)*em12621)) ≤ scalar12621.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12621:ℝ)) (by norm_num [ep12621]) ?_)
      (show bp12621^8 ≤ scalar12621.upperTail by norm_num [bp12621, scalar12621])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12621, bp12621, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12621:ℝ)) (by norm_num [em12621]) ?_)
      (show bm12621^8 ≤ scalar12621.lowerTail by norm_num [bm12621, scalar12621])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12621, bm12621, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12621 :
    agent12621.root+dsL+scalar12621.worldRadius < √(1/100/aL) ∧
    2*(agent12621.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12621, agent12621, scalar12621, tp12621, tm12621, ep12621, em12621, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12621, agent12621, scalar12621, tp12621, tm12621, ep12621, em12621, dsL]

noncomputable def master12621 : MasterCertificate 12621 world12621 agent12621 :=
  master scalar12621 dsL tp12621 tm12621 ep12621 em12621
    (by norm_num [dsL]) (by norm_num [tp12621]) (by norm_num [tm12621])
    (by norm_num [ep12621]) (by norm_num [em12621])
    positive12621 negative12621 tails12621.1 tails12621.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12621.1 tailGuards12621.2

theorem preserves12621 : master12621.toScalarCertificate = scalar12621 := rfl

noncomputable def tp12622 : ℝ := (577285311 / 2500000000)
noncomputable def tm12622 : ℝ := (-((1209320853 / 2000000000)))
noncomputable def ep12622 : ℝ := (51205185577365983 / 100000000000000000000)
noncomputable def em12622 : ℝ := (49918549405250253 / 100000000000000000000)
noncomputable def bp12622 : ℝ := (22289889499459596113 / 50000000000000000000)
noncomputable def bm12622 : ℝ := (45493991975636392637 / 100000000000000000000)

theorem positive12622 :
    Eplus aL (agent12622.root+dsL) scalar12622.worldRadius world12622.frame
      agent12622.frame tp12622 ≤ -ep12622 := by
  apply positive_check (eT := (115571239944978359669 / 100000000000000000000)) (y := (3780390317894260247 / 10000000000000000000)) (u := (145941990553454912241 / 100000000000000000000))
  · norm_num [world12622, agent12622, scalar12622, tp12622, tm12622, ep12622, em12622, dsL]
  · norm_num [world12622, agent12622, scalar12622, tp12622, tm12622, ep12622, em12622, dsL]
  · norm_num [world12622, agent12622, scalar12622, tp12622, tm12622, ep12622, em12622, dsL]
  · norm_num [world12622, agent12622, scalar12622, tp12622, tm12622, ep12622, em12622, dsL]
  · norm_num [world12622, agent12622, scalar12622, tp12622, tm12622, ep12622, em12622, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12622, agent12622, tp12622, tm12622, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12622, agent12622, scalar12622, tp12622, tm12622, ep12622, em12622, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12622, agent12622, tp12622, tm12622, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12622, agent12622, scalar12622, tp12622, tm12622, ep12622, em12622, dsL]

theorem negative12622 :
    Eminus aL (agent12622.root+dsL) scalar12622.worldRadius world12622.frame
      agent12622.frame tm12622 ≤ -em12622 := by
  apply negative_check (lo := (6845807147731442973 / 10000000000000000000)) (hi := (68458071477314429731 / 100000000000000000000))
    (y := (-((71695737543247348853 / 100000000000000000000)))) (u := (24411775784460984211 / 50000000000000000000))
  · norm_num [world12622, agent12622, scalar12622, tp12622, tm12622, ep12622, em12622, dsL]
  · norm_num [world12622, agent12622, scalar12622, tp12622, tm12622, ep12622, em12622, dsL]
  · norm_num [world12622, agent12622, scalar12622, tp12622, tm12622, ep12622, em12622, dsL]
  · norm_num [world12622, agent12622, scalar12622, tp12622, tm12622, ep12622, em12622, dsL]
  · norm_num [world12622, agent12622, scalar12622, tp12622, tm12622, ep12622, em12622, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12622, agent12622, tp12622, tm12622, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12622, agent12622, tp12622, tm12622, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12622, agent12622, scalar12622, tp12622, tm12622, ep12622, em12622, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12622, agent12622, tp12622, tm12622, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12622, agent12622, scalar12622, tp12622, tm12622, ep12622, em12622, dsL]

theorem tails12622 :
    exp (-((12622:ℝ)*ep12622)) ≤ scalar12622.upperTail ∧
    exp (-((12622:ℝ)*em12622)) ≤ scalar12622.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12622:ℝ)) (by norm_num [ep12622]) ?_)
      (show bp12622^8 ≤ scalar12622.upperTail by norm_num [bp12622, scalar12622])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12622, bp12622, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12622:ℝ)) (by norm_num [em12622]) ?_)
      (show bm12622^8 ≤ scalar12622.lowerTail by norm_num [bm12622, scalar12622])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12622, bm12622, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12622 :
    agent12622.root+dsL+scalar12622.worldRadius < √(1/100/aL) ∧
    2*(agent12622.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12622, agent12622, scalar12622, tp12622, tm12622, ep12622, em12622, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12622, agent12622, scalar12622, tp12622, tm12622, ep12622, em12622, dsL]

noncomputable def master12622 : MasterCertificate 12622 world12622 agent12622 :=
  master scalar12622 dsL tp12622 tm12622 ep12622 em12622
    (by norm_num [dsL]) (by norm_num [tp12622]) (by norm_num [tm12622])
    (by norm_num [ep12622]) (by norm_num [em12622])
    positive12622 negative12622 tails12622.1 tails12622.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12622.1 tailGuards12622.2

theorem preserves12622 : master12622.toScalarCertificate = scalar12622 := rfl

noncomputable def tp12623 : ℝ := (577307319 / 2500000000)
noncomputable def tm12623 : ℝ := (-((6046793451 / 10000000000)))
noncomputable def ep12623 : ℝ := (10241580766573667 / 20000000000000000000)
noncomputable def em12623 : ℝ := (9984177235279363 / 20000000000000000000)
noncomputable def bp12623 : ℝ := (44575013802027550973 / 100000000000000000000)
noncomputable def bm12623 : ℝ := (11372369008323095001 / 25000000000000000000)

theorem positive12623 :
    Eplus aL (agent12623.root+dsL) scalar12623.worldRadius world12623.frame
      agent12623.frame tp12623 ≤ -ep12623 := by
  apply positive_check (eT := (14446437933861628187 / 12500000000000000000)) (y := (1512189180867658951 / 4000000000000000000)) (u := (4560724891859193481 / 3125000000000000000))
  · norm_num [world12623, agent12623, scalar12623, tp12623, tm12623, ep12623, em12623, dsL]
  · norm_num [world12623, agent12623, scalar12623, tp12623, tm12623, ep12623, em12623, dsL]
  · norm_num [world12623, agent12623, scalar12623, tp12623, tm12623, ep12623, em12623, dsL]
  · norm_num [world12623, agent12623, scalar12623, tp12623, tm12623, ep12623, em12623, dsL]
  · norm_num [world12623, agent12623, scalar12623, tp12623, tm12623, ep12623, em12623, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12623, agent12623, tp12623, tm12623, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12623, agent12623, scalar12623, tp12623, tm12623, ep12623, em12623, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12623, agent12623, tp12623, tm12623, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12623, agent12623, scalar12623, tp12623, tm12623, ep12623, em12623, dsL]

theorem negative12623 :
    Eminus aL (agent12623.root+dsL) scalar12623.worldRadius world12623.frame
      agent12623.frame tm12623 ≤ -em12623 := by
  apply negative_check (lo := (34228920022268107959 / 50000000000000000000)) (hi := (68457840044536215919 / 100000000000000000000))
    (y := (-((17923961399132976943 / 25000000000000000000)))) (u := (48823498813499361873 / 100000000000000000000))
  · norm_num [world12623, agent12623, scalar12623, tp12623, tm12623, ep12623, em12623, dsL]
  · norm_num [world12623, agent12623, scalar12623, tp12623, tm12623, ep12623, em12623, dsL]
  · norm_num [world12623, agent12623, scalar12623, tp12623, tm12623, ep12623, em12623, dsL]
  · norm_num [world12623, agent12623, scalar12623, tp12623, tm12623, ep12623, em12623, dsL]
  · norm_num [world12623, agent12623, scalar12623, tp12623, tm12623, ep12623, em12623, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12623, agent12623, tp12623, tm12623, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12623, agent12623, tp12623, tm12623, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12623, agent12623, scalar12623, tp12623, tm12623, ep12623, em12623, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12623, agent12623, tp12623, tm12623, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12623, agent12623, scalar12623, tp12623, tm12623, ep12623, em12623, dsL]

theorem tails12623 :
    exp (-((12623:ℝ)*ep12623)) ≤ scalar12623.upperTail ∧
    exp (-((12623:ℝ)*em12623)) ≤ scalar12623.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12623:ℝ)) (by norm_num [ep12623]) ?_)
      (show bp12623^8 ≤ scalar12623.upperTail by norm_num [bp12623, scalar12623])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12623, bp12623, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12623:ℝ)) (by norm_num [em12623]) ?_)
      (show bm12623^8 ≤ scalar12623.lowerTail by norm_num [bm12623, scalar12623])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12623, bm12623, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12623 :
    agent12623.root+dsL+scalar12623.worldRadius < √(1/100/aL) ∧
    2*(agent12623.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12623, agent12623, scalar12623, tp12623, tm12623, ep12623, em12623, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12623, agent12623, scalar12623, tp12623, tm12623, ep12623, em12623, dsL]

noncomputable def master12623 : MasterCertificate 12623 world12623 agent12623 :=
  master scalar12623 dsL tp12623 tm12623 ep12623 em12623
    (by norm_num [dsL]) (by norm_num [tp12623]) (by norm_num [tm12623])
    (by norm_num [ep12623]) (by norm_num [em12623])
    positive12623 negative12623 tails12623.1 tails12623.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12623.1 tailGuards12623.2

theorem preserves12623 : master12623.toScalarCertificate = scalar12623 := rfl

noncomputable def tp12624 : ℝ := (1154658637 / 5000000000)
noncomputable def tm12624 : ℝ := (-((6046982611 / 10000000000)))
noncomputable def ep12624 : ℝ := (51210621564193773 / 100000000000000000000)
noncomputable def em12624 : ℝ := (9984644489648503 / 20000000000000000000)
noncomputable def bp12624 : ℝ := (11142562295068676273 / 25000000000000000000)
noncomputable def bm12624 : ℝ := (11371240157969048277 / 25000000000000000000)

theorem positive12624 :
    Eplus aL (agent12624.root+dsL) scalar12624.worldRadius world12624.frame
      agent12624.frame tp12624 ≤ -ep12624 := by
  apply positive_check (eT := (57785883391555964683 / 50000000000000000000)) (y := (9451388887695968507 / 25000000000000000000)) (u := (72972201038867513967 / 50000000000000000000))
  · norm_num [world12624, agent12624, scalar12624, tp12624, tm12624, ep12624, em12624, dsL]
  · norm_num [world12624, agent12624, scalar12624, tp12624, tm12624, ep12624, em12624, dsL]
  · norm_num [world12624, agent12624, scalar12624, tp12624, tm12624, ep12624, em12624, dsL]
  · norm_num [world12624, agent12624, scalar12624, tp12624, tm12624, ep12624, em12624, dsL]
  · norm_num [world12624, agent12624, scalar12624, tp12624, tm12624, ep12624, em12624, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12624, agent12624, tp12624, tm12624, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12624, agent12624, scalar12624, tp12624, tm12624, ep12624, em12624, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12624, agent12624, tp12624, tm12624, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12624, agent12624, scalar12624, tp12624, tm12624, ep12624, em12624, dsL]

theorem negative12624 :
    Eminus aL (agent12624.root+dsL) scalar12624.worldRadius world12624.frame
      agent12624.frame tm12624 ≤ -em12624 := by
  apply negative_check (lo := (68457608666588032007 / 100000000000000000000)) (hi := (8557201083323504001 / 12500000000000000000))
    (y := (-((14339190823478491209 / 20000000000000000000)))) (u := (976468916596940977 / 2000000000000000000))
  · norm_num [world12624, agent12624, scalar12624, tp12624, tm12624, ep12624, em12624, dsL]
  · norm_num [world12624, agent12624, scalar12624, tp12624, tm12624, ep12624, em12624, dsL]
  · norm_num [world12624, agent12624, scalar12624, tp12624, tm12624, ep12624, em12624, dsL]
  · norm_num [world12624, agent12624, scalar12624, tp12624, tm12624, ep12624, em12624, dsL]
  · norm_num [world12624, agent12624, scalar12624, tp12624, tm12624, ep12624, em12624, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12624, agent12624, tp12624, tm12624, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12624, agent12624, tp12624, tm12624, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12624, agent12624, scalar12624, tp12624, tm12624, ep12624, em12624, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12624, agent12624, tp12624, tm12624, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12624, agent12624, scalar12624, tp12624, tm12624, ep12624, em12624, dsL]

theorem tails12624 :
    exp (-((12624:ℝ)*ep12624)) ≤ scalar12624.upperTail ∧
    exp (-((12624:ℝ)*em12624)) ≤ scalar12624.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12624:ℝ)) (by norm_num [ep12624]) ?_)
      (show bp12624^8 ≤ scalar12624.upperTail by norm_num [bp12624, scalar12624])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12624, bp12624, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12624:ℝ)) (by norm_num [em12624]) ?_)
      (show bm12624^8 ≤ scalar12624.lowerTail by norm_num [bm12624, scalar12624])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12624, bm12624, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12624 :
    agent12624.root+dsL+scalar12624.worldRadius < √(1/100/aL) ∧
    2*(agent12624.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12624, agent12624, scalar12624, tp12624, tm12624, ep12624, em12624, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12624, agent12624, scalar12624, tp12624, tm12624, ep12624, em12624, dsL]

noncomputable def master12624 : MasterCertificate 12624 world12624 agent12624 :=
  master scalar12624 dsL tp12624 tm12624 ep12624 em12624
    (by norm_num [dsL]) (by norm_num [tp12624]) (by norm_num [tm12624])
    (by norm_num [ep12624]) (by norm_num [em12624])
    positive12624 negative12624 tails12624.1 tails12624.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12624.1 tailGuards12624.2

theorem preserves12624 : master12624.toScalarCertificate = scalar12624 := rfl

end BstLean.Part268
