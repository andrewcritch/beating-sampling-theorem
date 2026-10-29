import BstLean.Part261Checker
import BstLean.Part268Scalar22
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12900 : ℝ := (2334342261 / 10000000000)
noncomputable def tm12900 : ℝ := (-((3051193451 / 5000000000)))
noncomputable def ep12900 : ℝ := (25976714084407263 / 50000000000000000000)
noncomputable def em12900 : ℝ := (50568509915043981 / 100000000000000000000)
noncomputable def bp12900 : ℝ := (8653667714666881817 / 20000000000000000000)
noncomputable def bm12900 : ℝ := (221227343424213051 / 500000000000000000)

theorem positive12900 :
    Eplus aL (agent12900.root+dsL) scalar12900.worldRadius world12900.frame
      agent12900.frame tp12900 ≤ -ep12900 := by
  apply positive_check (eT := (28912742301314429863 / 25000000000000000000)) (y := (37998312603308694639 / 100000000000000000000)) (u := (146225991510062248013 / 100000000000000000000))
  · norm_num [world12900, agent12900, scalar12900, tp12900, tm12900, ep12900, em12900, dsL]
  · norm_num [world12900, agent12900, scalar12900, tp12900, tm12900, ep12900, em12900, dsL]
  · norm_num [world12900, agent12900, scalar12900, tp12900, tm12900, ep12900, em12900, dsL]
  · norm_num [world12900, agent12900, scalar12900, tp12900, tm12900, ep12900, em12900, dsL]
  · norm_num [world12900, agent12900, scalar12900, tp12900, tm12900, ep12900, em12900, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12900, agent12900, tp12900, tm12900, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12900, agent12900, scalar12900, tp12900, tm12900, ep12900, em12900, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12900, agent12900, tp12900, tm12900, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12900, agent12900, scalar12900, tp12900, tm12900, ep12900, em12900, dsL]

theorem negative12900 :
    Eminus aL (agent12900.root+dsL) scalar12900.worldRadius world12900.frame
      agent12900.frame tm12900 ≤ -em12900 := by
  apply negative_check (lo := (4273626346194171859 / 6250000000000000000)) (hi := (13675604307821349949 / 20000000000000000000))
    (y := (-((71656088796624455923 / 100000000000000000000)))) (u := (48842913333270629079 / 100000000000000000000))
  · norm_num [world12900, agent12900, scalar12900, tp12900, tm12900, ep12900, em12900, dsL]
  · norm_num [world12900, agent12900, scalar12900, tp12900, tm12900, ep12900, em12900, dsL]
  · norm_num [world12900, agent12900, scalar12900, tp12900, tm12900, ep12900, em12900, dsL]
  · norm_num [world12900, agent12900, scalar12900, tp12900, tm12900, ep12900, em12900, dsL]
  · norm_num [world12900, agent12900, scalar12900, tp12900, tm12900, ep12900, em12900, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12900, agent12900, tp12900, tm12900, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12900, agent12900, tp12900, tm12900, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12900, agent12900, scalar12900, tp12900, tm12900, ep12900, em12900, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12900, agent12900, tp12900, tm12900, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12900, agent12900, scalar12900, tp12900, tm12900, ep12900, em12900, dsL]

theorem tails12900 :
    exp (-((12900:ℝ)*ep12900)) ≤ scalar12900.upperTail ∧
    exp (-((12900:ℝ)*em12900)) ≤ scalar12900.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12900:ℝ)) (by norm_num [ep12900]) ?_)
      (show bp12900^8 ≤ scalar12900.upperTail by norm_num [bp12900, scalar12900])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12900, bp12900, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12900:ℝ)) (by norm_num [em12900]) ?_)
      (show bm12900^8 ≤ scalar12900.lowerTail by norm_num [bm12900, scalar12900])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12900, bm12900, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12900 :
    agent12900.root+dsL+scalar12900.worldRadius < √(1/100/aL) ∧
    2*(agent12900.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12900, agent12900, scalar12900, tp12900, tm12900, ep12900, em12900, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12900, agent12900, scalar12900, tp12900, tm12900, ep12900, em12900, dsL]

noncomputable def master12900 : MasterCertificate 12900 world12900 agent12900 :=
  master scalar12900 dsL tp12900 tm12900 ep12900 em12900
    (by norm_num [dsL]) (by norm_num [tp12900]) (by norm_num [tm12900])
    (by norm_num [ep12900]) (by norm_num [em12900])
    positive12900 negative12900 tails12900.1 tails12900.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12900.1 tailGuards12900.2

theorem preserves12900 : master12900.toScalarCertificate = scalar12900 := rfl

noncomputable def tp12901 : ℝ := (1167210451 / 5000000000)
noncomputable def tm12901 : ℝ := (-((190704829 / 312500000)))
noncomputable def ep12901 : ℝ := (51955815933651181 / 100000000000000000000)
noncomputable def em12901 : ℝ := (10114109223359601 / 20000000000000000000)
noncomputable def bp12901 : ℝ := (10815965701085805273 / 25000000000000000000)
noncomputable def bm12901 : ℝ := (22120609623611329321 / 50000000000000000000)

theorem positive12901 :
    Eplus aL (agent12901.root+dsL) scalar12901.worldRadius world12901.frame
      agent12901.frame tp12901 ≤ -ep12901 := by
  apply positive_check (eT := (28912793428081566423 / 25000000000000000000)) (y := (3799903279009983111 / 10000000000000000000)) (u := (29245408922826093093 / 20000000000000000000))
  · norm_num [world12901, agent12901, scalar12901, tp12901, tm12901, ep12901, em12901, dsL]
  · norm_num [world12901, agent12901, scalar12901, tp12901, tm12901, ep12901, em12901, dsL]
  · norm_num [world12901, agent12901, scalar12901, tp12901, tm12901, ep12901, em12901, dsL]
  · norm_num [world12901, agent12901, scalar12901, tp12901, tm12901, ep12901, em12901, dsL]
  · norm_num [world12901, agent12901, scalar12901, tp12901, tm12901, ep12901, em12901, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12901, agent12901, tp12901, tm12901, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12901, agent12901, scalar12901, tp12901, tm12901, ep12901, em12901, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12901, agent12901, tp12901, tm12901, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12901, agent12901, scalar12901, tp12901, tm12901, ep12901, em12901, dsL]

theorem negative12901 :
    Eminus aL (agent12901.root+dsL) scalar12901.worldRadius world12901.frame
      agent12901.frame tm12901 ≤ -em12901 := by
  apply negative_check (lo := (68377867109526647523 / 100000000000000000000)) (hi := (17094466777381661881 / 25000000000000000000))
    (y := (-((71656078571679989493 / 100000000000000000000)))) (u := (24421459163715824259 / 50000000000000000000))
  · norm_num [world12901, agent12901, scalar12901, tp12901, tm12901, ep12901, em12901, dsL]
  · norm_num [world12901, agent12901, scalar12901, tp12901, tm12901, ep12901, em12901, dsL]
  · norm_num [world12901, agent12901, scalar12901, tp12901, tm12901, ep12901, em12901, dsL]
  · norm_num [world12901, agent12901, scalar12901, tp12901, tm12901, ep12901, em12901, dsL]
  · norm_num [world12901, agent12901, scalar12901, tp12901, tm12901, ep12901, em12901, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12901, agent12901, tp12901, tm12901, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12901, agent12901, tp12901, tm12901, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12901, agent12901, scalar12901, tp12901, tm12901, ep12901, em12901, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12901, agent12901, tp12901, tm12901, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12901, agent12901, scalar12901, tp12901, tm12901, ep12901, em12901, dsL]

theorem tails12901 :
    exp (-((12901:ℝ)*ep12901)) ≤ scalar12901.upperTail ∧
    exp (-((12901:ℝ)*em12901)) ≤ scalar12901.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12901:ℝ)) (by norm_num [ep12901]) ?_)
      (show bp12901^8 ≤ scalar12901.upperTail by norm_num [bp12901, scalar12901])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12901, bp12901, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12901:ℝ)) (by norm_num [em12901]) ?_)
      (show bm12901^8 ≤ scalar12901.lowerTail by norm_num [bm12901, scalar12901])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12901, bm12901, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12901 :
    agent12901.root+dsL+scalar12901.worldRadius < √(1/100/aL) ∧
    2*(agent12901.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12901, agent12901, scalar12901, tp12901, tm12901, ep12901, em12901, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12901, agent12901, scalar12901, tp12901, tm12901, ep12901, em12901, dsL]

noncomputable def master12901 : MasterCertificate 12901 world12901 agent12901 :=
  master scalar12901 dsL tp12901 tm12901 ep12901 em12901
    (by norm_num [dsL]) (by norm_num [tp12901]) (by norm_num [tm12901])
    (by norm_num [ep12901]) (by norm_num [em12901])
    positive12901 negative12901 tails12901.1 tails12901.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12901.1 tailGuards12901.2

theorem preserves12901 : master12901.toScalarCertificate = scalar12901 := rfl

noncomputable def tp12902 : ℝ := (583624879 / 2500000000)
noncomputable def tm12902 : ℝ := (-((1525680543 / 2500000000)))
noncomputable def ep12902 : ℝ := (25979101367519841 / 50000000000000000000)
noncomputable def em12902 : ℝ := (50572581394377749 / 100000000000000000000)
noncomputable def bp12902 : ℝ := (21629693956133395253 / 50000000000000000000)
noncomputable def bm12902 : ℝ := (44236970651875343271 / 100000000000000000000)

theorem positive12902 :
    Eplus aL (agent12902.root+dsL) scalar12902.worldRadius world12902.frame
      agent12902.frame tp12902 ≤ -ep12902 := by
  apply positive_check (eT := (115651378057861797823 / 100000000000000000000)) (y := (7599950588869450469 / 20000000000000000000)) (u := (146228097678194970913 / 100000000000000000000))
  · norm_num [world12902, agent12902, scalar12902, tp12902, tm12902, ep12902, em12902, dsL]
  · norm_num [world12902, agent12902, scalar12902, tp12902, tm12902, ep12902, em12902, dsL]
  · norm_num [world12902, agent12902, scalar12902, tp12902, tm12902, ep12902, em12902, dsL]
  · norm_num [world12902, agent12902, scalar12902, tp12902, tm12902, ep12902, em12902, dsL]
  · norm_num [world12902, agent12902, scalar12902, tp12902, tm12902, ep12902, em12902, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12902, agent12902, tp12902, tm12902, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12902, agent12902, scalar12902, tp12902, tm12902, ep12902, em12902, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12902, agent12902, tp12902, tm12902, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12902, agent12902, scalar12902, tp12902, tm12902, ep12902, em12902, dsL]

theorem negative12902 :
    Eminus aL (agent12902.root+dsL) scalar12902.worldRadius world12902.frame
      agent12902.frame tm12902 ≤ -em12902 := by
  apply negative_check (lo := (17094428136570179301 / 25000000000000000000)) (hi := (13675542509256143441 / 20000000000000000000))
    (y := (-((71656069312542264139 / 100000000000000000000)))) (u := (24421461424932467453 / 50000000000000000000))
  · norm_num [world12902, agent12902, scalar12902, tp12902, tm12902, ep12902, em12902, dsL]
  · norm_num [world12902, agent12902, scalar12902, tp12902, tm12902, ep12902, em12902, dsL]
  · norm_num [world12902, agent12902, scalar12902, tp12902, tm12902, ep12902, em12902, dsL]
  · norm_num [world12902, agent12902, scalar12902, tp12902, tm12902, ep12902, em12902, dsL]
  · norm_num [world12902, agent12902, scalar12902, tp12902, tm12902, ep12902, em12902, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12902, agent12902, tp12902, tm12902, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12902, agent12902, tp12902, tm12902, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12902, agent12902, scalar12902, tp12902, tm12902, ep12902, em12902, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12902, agent12902, tp12902, tm12902, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12902, agent12902, scalar12902, tp12902, tm12902, ep12902, em12902, dsL]

theorem tails12902 :
    exp (-((12902:ℝ)*ep12902)) ≤ scalar12902.upperTail ∧
    exp (-((12902:ℝ)*em12902)) ≤ scalar12902.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12902:ℝ)) (by norm_num [ep12902]) ?_)
      (show bp12902^8 ≤ scalar12902.upperTail by norm_num [bp12902, scalar12902])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12902, bp12902, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12902:ℝ)) (by norm_num [em12902]) ?_)
      (show bm12902^8 ≤ scalar12902.lowerTail by norm_num [bm12902, scalar12902])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12902, bm12902, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12902 :
    agent12902.root+dsL+scalar12902.worldRadius < √(1/100/aL) ∧
    2*(agent12902.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12902, agent12902, scalar12902, tp12902, tm12902, ep12902, em12902, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12902, agent12902, scalar12902, tp12902, tm12902, ep12902, em12902, dsL]

noncomputable def master12902 : MasterCertificate 12902 world12902 agent12902 :=
  master scalar12902 dsL tp12902 tm12902 ep12902 em12902
    (by norm_num [dsL]) (by norm_num [tp12902]) (by norm_num [tm12902])
    (by norm_num [ep12902]) (by norm_num [em12902])
    positive12902 negative12902 tails12902.1 tails12902.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12902.1 tailGuards12902.2

theorem preserves12902 : master12902.toScalarCertificate = scalar12902 := rfl

noncomputable def tp12903 : ℝ := (233457811 / 1000000000)
noncomputable def tm12903 : ℝ := (-((1220577911 / 2000000000)))
noncomputable def ep12903 : ℝ := (5196058810572833 / 10000000000000000000)
noncomputable def em12903 : ℝ := (50574615377284717 / 100000000000000000000)
noncomputable def bp12903 : ℝ := (5406864277882766399 / 12500000000000000000)
noncomputable def bm12903 : ℝ := (44232723163110178379 / 100000000000000000000)

theorem positive12903 :
    Eplus aL (agent12903.root+dsL) scalar12903.worldRadius world12903.frame
      agent12903.frame tp12903 ≤ -ep12903 := by
  apply positive_check (eT := (115651582292279219087 / 100000000000000000000)) (y := (38000473034227699433 / 100000000000000000000)) (u := (146229150655719909629 / 100000000000000000000))
  · norm_num [world12903, agent12903, scalar12903, tp12903, tm12903, ep12903, em12903, dsL]
  · norm_num [world12903, agent12903, scalar12903, tp12903, tm12903, ep12903, em12903, dsL]
  · norm_num [world12903, agent12903, scalar12903, tp12903, tm12903, ep12903, em12903, dsL]
  · norm_num [world12903, agent12903, scalar12903, tp12903, tm12903, ep12903, em12903, dsL]
  · norm_num [world12903, agent12903, scalar12903, tp12903, tm12903, ep12903, em12903, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12903, agent12903, tp12903, tm12903, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12903, agent12903, scalar12903, tp12903, tm12903, ep12903, em12903, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12903, agent12903, tp12903, tm12903, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12903, agent12903, scalar12903, tp12903, tm12903, ep12903, em12903, dsL]

theorem negative12903 :
    Eminus aL (agent12903.root+dsL) scalar12903.worldRadius world12903.frame
      agent12903.frame tm12903 ≤ -em12903 := by
  apply negative_check (lo := (17094389759415822579 / 25000000000000000000)) (hi := (68377559037663290317 / 100000000000000000000))
    (y := (-((35828029016446937317 / 50000000000000000000)))) (u := (48842928359175206243 / 100000000000000000000))
  · norm_num [world12903, agent12903, scalar12903, tp12903, tm12903, ep12903, em12903, dsL]
  · norm_num [world12903, agent12903, scalar12903, tp12903, tm12903, ep12903, em12903, dsL]
  · norm_num [world12903, agent12903, scalar12903, tp12903, tm12903, ep12903, em12903, dsL]
  · norm_num [world12903, agent12903, scalar12903, tp12903, tm12903, ep12903, em12903, dsL]
  · norm_num [world12903, agent12903, scalar12903, tp12903, tm12903, ep12903, em12903, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12903, agent12903, tp12903, tm12903, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12903, agent12903, tp12903, tm12903, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12903, agent12903, scalar12903, tp12903, tm12903, ep12903, em12903, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12903, agent12903, tp12903, tm12903, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12903, agent12903, scalar12903, tp12903, tm12903, ep12903, em12903, dsL]

theorem tails12903 :
    exp (-((12903:ℝ)*ep12903)) ≤ scalar12903.upperTail ∧
    exp (-((12903:ℝ)*em12903)) ≤ scalar12903.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12903:ℝ)) (by norm_num [ep12903]) ?_)
      (show bp12903^8 ≤ scalar12903.upperTail by norm_num [bp12903, scalar12903])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12903, bp12903, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12903:ℝ)) (by norm_num [em12903]) ?_)
      (show bm12903^8 ≤ scalar12903.lowerTail by norm_num [bm12903, scalar12903])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12903, bm12903, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12903 :
    agent12903.root+dsL+scalar12903.worldRadius < √(1/100/aL) ∧
    2*(agent12903.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12903, agent12903, scalar12903, tp12903, tm12903, ep12903, em12903, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12903, agent12903, scalar12903, tp12903, tm12903, ep12903, em12903, dsL]

noncomputable def master12903 : MasterCertificate 12903 world12903 agent12903 :=
  master scalar12903 dsL tp12903 tm12903 ep12903 em12903
    (by norm_num [dsL]) (by norm_num [tp12903]) (by norm_num [tm12903])
    (by norm_num [ep12903]) (by norm_num [em12903])
    positive12903 negative12903 tails12903.1 tails12903.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12903.1 tailGuards12903.2

theorem preserves12903 : master12903.toScalarCertificate = scalar12903 := rfl

noncomputable def tp12904 : ℝ := (583664143 / 2500000000)
noncomputable def tm12904 : ℝ := (-((3051528509 / 5000000000)))
noncomputable def ep12904 : ℝ := (25981485940162763 / 50000000000000000000)
noncomputable def em12904 : ℝ := (2023065915575627 / 4000000000000000000)
noncomputable def bp12904 : ℝ := (21625220926032951807 / 50000000000000000000)
noncomputable def bm12904 : ℝ := (22114238453276154033 / 50000000000000000000)

theorem positive12904 :
    Eplus aL (agent12904.root+dsL) scalar12904.worldRadius world12904.frame
      agent12904.frame tp12904 ≤ -ep12904 := by
  apply positive_check (eT := (115651785608817841591 / 100000000000000000000)) (y := (9500297787749125353 / 25000000000000000000)) (u := (73115100377771056003 / 50000000000000000000))
  · norm_num [world12904, agent12904, scalar12904, tp12904, tm12904, ep12904, em12904, dsL]
  · norm_num [world12904, agent12904, scalar12904, tp12904, tm12904, ep12904, em12904, dsL]
  · norm_num [world12904, agent12904, scalar12904, tp12904, tm12904, ep12904, em12904, dsL]
  · norm_num [world12904, agent12904, scalar12904, tp12904, tm12904, ep12904, em12904, dsL]
  · norm_num [world12904, agent12904, scalar12904, tp12904, tm12904, ep12904, em12904, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12904, agent12904, tp12904, tm12904, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12904, agent12904, scalar12904, tp12904, tm12904, ep12904, em12904, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12904, agent12904, tp12904, tm12904, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12904, agent12904, scalar12904, tp12904, tm12904, ep12904, em12904, dsL]

theorem negative12904 :
    Eminus aL (agent12904.root+dsL) scalar12904.worldRadius world12904.frame
      agent12904.frame tm12904 ≤ -em12904 := by
  apply negative_check (lo := (68377405131312295571 / 100000000000000000000)) (hi := (17094351282828073893 / 25000000000000000000))
    (y := (-((17914011974696801891 / 25000000000000000000)))) (u := (12210733327242479073 / 25000000000000000000))
  · norm_num [world12904, agent12904, scalar12904, tp12904, tm12904, ep12904, em12904, dsL]
  · norm_num [world12904, agent12904, scalar12904, tp12904, tm12904, ep12904, em12904, dsL]
  · norm_num [world12904, agent12904, scalar12904, tp12904, tm12904, ep12904, em12904, dsL]
  · norm_num [world12904, agent12904, scalar12904, tp12904, tm12904, ep12904, em12904, dsL]
  · norm_num [world12904, agent12904, scalar12904, tp12904, tm12904, ep12904, em12904, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12904, agent12904, tp12904, tm12904, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12904, agent12904, tp12904, tm12904, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12904, agent12904, scalar12904, tp12904, tm12904, ep12904, em12904, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12904, agent12904, tp12904, tm12904, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12904, agent12904, scalar12904, tp12904, tm12904, ep12904, em12904, dsL]

theorem tails12904 :
    exp (-((12904:ℝ)*ep12904)) ≤ scalar12904.upperTail ∧
    exp (-((12904:ℝ)*em12904)) ≤ scalar12904.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12904:ℝ)) (by norm_num [ep12904]) ?_)
      (show bp12904^8 ≤ scalar12904.upperTail by norm_num [bp12904, scalar12904])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12904, bp12904, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12904:ℝ)) (by norm_num [em12904]) ?_)
      (show bm12904^8 ≤ scalar12904.lowerTail by norm_num [bm12904, scalar12904])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12904, bm12904, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12904 :
    agent12904.root+dsL+scalar12904.worldRadius < √(1/100/aL) ∧
    2*(agent12904.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12904, agent12904, scalar12904, tp12904, tm12904, ep12904, em12904, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12904, agent12904, scalar12904, tp12904, tm12904, ep12904, em12904, dsL]

noncomputable def master12904 : MasterCertificate 12904 world12904 agent12904 :=
  master scalar12904 dsL tp12904 tm12904 ep12904 em12904
    (by norm_num [dsL]) (by norm_num [tp12904]) (by norm_num [tm12904])
    (by norm_num [ep12904]) (by norm_num [em12904])
    positive12904 negative12904 tails12904.1 tails12904.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12904.1 tailGuards12904.2

theorem preserves12904 : master12904.toScalarCertificate = scalar12904 := rfl

noncomputable def tp12905 : ℝ := (2334735027 / 10000000000)
noncomputable def tm12905 : ℝ := (-((610322429 / 1000000000)))
noncomputable def ep12905 : ℝ := (5196535516701133 / 10000000000000000000)
noncomputable def em12905 : ℝ := (25289339958904659 / 50000000000000000000)
noncomputable def bp12905 : ℝ := (43245970026144500507 / 100000000000000000000)
noncomputable def bm12905 : ℝ := (22112115588984965293 / 50000000000000000000)

theorem positive12905 :
    Eplus aL (agent12905.root+dsL) scalar12905.worldRadius world12905.frame
      agent12905.frame tp12905 ≤ -ep12905 := by
  apply positive_check (eT := (4626079556316553971 / 4000000000000000000)) (y := (38001909535429499601 / 100000000000000000000)) (u := (73115625627156993563 / 50000000000000000000))
  · norm_num [world12905, agent12905, scalar12905, tp12905, tm12905, ep12905, em12905, dsL]
  · norm_num [world12905, agent12905, scalar12905, tp12905, tm12905, ep12905, em12905, dsL]
  · norm_num [world12905, agent12905, scalar12905, tp12905, tm12905, ep12905, em12905, dsL]
  · norm_num [world12905, agent12905, scalar12905, tp12905, tm12905, ep12905, em12905, dsL]
  · norm_num [world12905, agent12905, scalar12905, tp12905, tm12905, ep12905, em12905, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12905, agent12905, tp12905, tm12905, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12905, agent12905, scalar12905, tp12905, tm12905, ep12905, em12905, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12905, agent12905, tp12905, tm12905, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12905, agent12905, scalar12905, tp12905, tm12905, ep12905, em12905, dsL]

theorem negative12905 :
    Eminus aL (agent12905.root+dsL) scalar12905.worldRadius world12905.frame
      agent12905.frame tm12905 ≤ -em12905 := by
  apply negative_check (lo := (68377251981414251989 / 100000000000000000000)) (hi := (6837725198141425199 / 10000000000000000000))
    (y := (-((3582801842030144567 / 5000000000000000000)))) (u := (24421469355055902841 / 50000000000000000000))
  · norm_num [world12905, agent12905, scalar12905, tp12905, tm12905, ep12905, em12905, dsL]
  · norm_num [world12905, agent12905, scalar12905, tp12905, tm12905, ep12905, em12905, dsL]
  · norm_num [world12905, agent12905, scalar12905, tp12905, tm12905, ep12905, em12905, dsL]
  · norm_num [world12905, agent12905, scalar12905, tp12905, tm12905, ep12905, em12905, dsL]
  · norm_num [world12905, agent12905, scalar12905, tp12905, tm12905, ep12905, em12905, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12905, agent12905, tp12905, tm12905, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12905, agent12905, tp12905, tm12905, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12905, agent12905, scalar12905, tp12905, tm12905, ep12905, em12905, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12905, agent12905, tp12905, tm12905, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12905, agent12905, scalar12905, tp12905, tm12905, ep12905, em12905, dsL]

theorem tails12905 :
    exp (-((12905:ℝ)*ep12905)) ≤ scalar12905.upperTail ∧
    exp (-((12905:ℝ)*em12905)) ≤ scalar12905.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12905:ℝ)) (by norm_num [ep12905]) ?_)
      (show bp12905^8 ≤ scalar12905.upperTail by norm_num [bp12905, scalar12905])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12905, bp12905, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12905:ℝ)) (by norm_num [em12905]) ?_)
      (show bm12905^8 ≤ scalar12905.lowerTail by norm_num [bm12905, scalar12905])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12905, bm12905, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12905 :
    agent12905.root+dsL+scalar12905.worldRadius < √(1/100/aL) ∧
    2*(agent12905.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12905, agent12905, scalar12905, tp12905, tm12905, ep12905, em12905, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12905, agent12905, scalar12905, tp12905, tm12905, ep12905, em12905, dsL]

noncomputable def master12905 : MasterCertificate 12905 world12905 agent12905 :=
  master scalar12905 dsL tp12905 tm12905 ep12905 em12905
    (by norm_num [dsL]) (by norm_num [tp12905]) (by norm_num [tm12905])
    (by norm_num [ep12905]) (by norm_num [em12905])
    positive12905 negative12905 tails12905.1 tails12905.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12905.1 tailGuards12905.2

theorem preserves12905 : master12905.toScalarCertificate = scalar12905 := rfl

noncomputable def tp12906 : ℝ := (2334813519 / 10000000000)
noncomputable def tm12906 : ℝ := (-((3051695753 / 5000000000)))
noncomputable def ep12906 : ℝ := (12991934138073071 / 25000000000000000000)
noncomputable def em12906 : ℝ := (50580710215390617 / 100000000000000000000)
noncomputable def bp12906 : ℝ := (8648299946269483897 / 20000000000000000000)
noncomputable def bm12906 : ℝ := (22109993433530009373 / 50000000000000000000)

theorem positive12906 :
    Eplus aL (agent12906.root+dsL) scalar12906.worldRadius world12906.frame
      agent12906.frame tp12906 ≤ -ep12906 := by
  apply positive_check (eT := (28913048126627750567 / 25000000000000000000)) (y := (38002628901222802149 / 100000000000000000000)) (u := (14623230319569827767 / 10000000000000000000))
  · norm_num [world12906, agent12906, scalar12906, tp12906, tm12906, ep12906, em12906, dsL]
  · norm_num [world12906, agent12906, scalar12906, tp12906, tm12906, ep12906, em12906, dsL]
  · norm_num [world12906, agent12906, scalar12906, tp12906, tm12906, ep12906, em12906, dsL]
  · norm_num [world12906, agent12906, scalar12906, tp12906, tm12906, ep12906, em12906, dsL]
  · norm_num [world12906, agent12906, scalar12906, tp12906, tm12906, ep12906, em12906, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12906, agent12906, tp12906, tm12906, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12906, agent12906, scalar12906, tp12906, tm12906, ep12906, em12906, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12906, agent12906, tp12906, tm12906, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12906, agent12906, scalar12906, tp12906, tm12906, ep12906, em12906, dsL]

theorem negative12906 :
    Eminus aL (agent12906.root+dsL) scalar12906.worldRadius world12906.frame
      agent12906.frame tm12906 ≤ -em12906 := by
  apply negative_check (lo := (17094274753245923619 / 25000000000000000000)) (hi := (68377099012983694477 / 100000000000000000000))
    (y := (-((35828012805891075871 / 50000000000000000000)))) (u := (24421472097299072657 / 50000000000000000000))
  · norm_num [world12906, agent12906, scalar12906, tp12906, tm12906, ep12906, em12906, dsL]
  · norm_num [world12906, agent12906, scalar12906, tp12906, tm12906, ep12906, em12906, dsL]
  · norm_num [world12906, agent12906, scalar12906, tp12906, tm12906, ep12906, em12906, dsL]
  · norm_num [world12906, agent12906, scalar12906, tp12906, tm12906, ep12906, em12906, dsL]
  · norm_num [world12906, agent12906, scalar12906, tp12906, tm12906, ep12906, em12906, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12906, agent12906, tp12906, tm12906, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12906, agent12906, tp12906, tm12906, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12906, agent12906, scalar12906, tp12906, tm12906, ep12906, em12906, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12906, agent12906, tp12906, tm12906, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12906, agent12906, scalar12906, tp12906, tm12906, ep12906, em12906, dsL]

theorem tails12906 :
    exp (-((12906:ℝ)*ep12906)) ≤ scalar12906.upperTail ∧
    exp (-((12906:ℝ)*em12906)) ≤ scalar12906.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12906:ℝ)) (by norm_num [ep12906]) ?_)
      (show bp12906^8 ≤ scalar12906.upperTail by norm_num [bp12906, scalar12906])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12906, bp12906, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12906:ℝ)) (by norm_num [em12906]) ?_)
      (show bm12906^8 ≤ scalar12906.lowerTail by norm_num [bm12906, scalar12906])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12906, bm12906, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12906 :
    agent12906.root+dsL+scalar12906.worldRadius < √(1/100/aL) ∧
    2*(agent12906.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12906, agent12906, scalar12906, tp12906, tm12906, ep12906, em12906, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12906, agent12906, scalar12906, tp12906, tm12906, ep12906, em12906, dsL]

noncomputable def master12906 : MasterCertificate 12906 world12906 agent12906 :=
  master scalar12906 dsL tp12906 tm12906 ep12906 em12906
    (by norm_num [dsL]) (by norm_num [tp12906]) (by norm_num [tm12906])
    (by norm_num [ep12906]) (by norm_num [em12906])
    positive12906 negative12906 tails12906.1 tails12906.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12906.1 tailGuards12906.2

theorem preserves12906 : master12906.toScalarCertificate = scalar12906 := rfl

noncomputable def tp12907 : ℝ := (1167445967 / 5000000000)
noncomputable def tm12907 : ℝ := (-((6103558681 / 10000000000)))
noncomputable def ep12907 : ℝ := (10394023394873303 / 20000000000000000000)
noncomputable def em12907 : ℝ := (12645684897294247 / 25000000000000000000)
noncomputable def bp12907 : ℝ := (108092575782849353 / 250000000000000000)
noncomputable def bm12907 : ℝ := (22107871699031593923 / 50000000000000000000)

theorem positive12907 :
    Eplus aL (agent12907.root+dsL) scalar12907.worldRadius world12907.frame
      agent12907.frame tp12907 ≤ -ep12907 := by
  apply positive_check (eT := (115652395583412228889 / 100000000000000000000)) (y := (19001673679674947357 / 50000000000000000000)) (u := (146233353817339155567 / 100000000000000000000))
  · norm_num [world12907, agent12907, scalar12907, tp12907, tm12907, ep12907, em12907, dsL]
  · norm_num [world12907, agent12907, scalar12907, tp12907, tm12907, ep12907, em12907, dsL]
  · norm_num [world12907, agent12907, scalar12907, tp12907, tm12907, ep12907, em12907, dsL]
  · norm_num [world12907, agent12907, scalar12907, tp12907, tm12907, ep12907, em12907, dsL]
  · norm_num [world12907, agent12907, scalar12907, tp12907, tm12907, ep12907, em12907, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12907, agent12907, tp12907, tm12907, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12907, agent12907, scalar12907, tp12907, tm12907, ep12907, em12907, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12907, agent12907, tp12907, tm12907, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12907, agent12907, scalar12907, tp12907, tm12907, ep12907, em12907, dsL]

theorem negative12907 :
    Eminus aL (agent12907.root+dsL) scalar12907.worldRadius world12907.frame
      agent12907.frame tm12907 ≤ -em12907 := by
  apply negative_check (lo := (68376946162201695301 / 100000000000000000000)) (hi := (34188473081100847651 / 50000000000000000000))
    (y := (-((71656014777984661293 / 100000000000000000000)))) (u := (48842949486144094367 / 100000000000000000000))
  · norm_num [world12907, agent12907, scalar12907, tp12907, tm12907, ep12907, em12907, dsL]
  · norm_num [world12907, agent12907, scalar12907, tp12907, tm12907, ep12907, em12907, dsL]
  · norm_num [world12907, agent12907, scalar12907, tp12907, tm12907, ep12907, em12907, dsL]
  · norm_num [world12907, agent12907, scalar12907, tp12907, tm12907, ep12907, em12907, dsL]
  · norm_num [world12907, agent12907, scalar12907, tp12907, tm12907, ep12907, em12907, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12907, agent12907, tp12907, tm12907, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12907, agent12907, tp12907, tm12907, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12907, agent12907, scalar12907, tp12907, tm12907, ep12907, em12907, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12907, agent12907, tp12907, tm12907, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12907, agent12907, scalar12907, tp12907, tm12907, ep12907, em12907, dsL]

theorem tails12907 :
    exp (-((12907:ℝ)*ep12907)) ≤ scalar12907.upperTail ∧
    exp (-((12907:ℝ)*em12907)) ≤ scalar12907.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12907:ℝ)) (by norm_num [ep12907]) ?_)
      (show bp12907^8 ≤ scalar12907.upperTail by norm_num [bp12907, scalar12907])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12907, bp12907, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12907:ℝ)) (by norm_num [em12907]) ?_)
      (show bm12907^8 ≤ scalar12907.lowerTail by norm_num [bm12907, scalar12907])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12907, bm12907, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12907 :
    agent12907.root+dsL+scalar12907.worldRadius < √(1/100/aL) ∧
    2*(agent12907.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12907, agent12907, scalar12907, tp12907, tm12907, ep12907, em12907, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12907, agent12907, scalar12907, tp12907, tm12907, ep12907, em12907, dsL]

noncomputable def master12907 : MasterCertificate 12907 world12907 agent12907 :=
  master scalar12907 dsL tp12907 tm12907 ep12907 em12907
    (by norm_num [dsL]) (by norm_num [tp12907]) (by norm_num [tm12907])
    (by norm_num [ep12907]) (by norm_num [em12907])
    positive12907 negative12907 tails12907.1 tails12907.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12907.1 tailGuards12907.2

theorem preserves12907 : master12907.toScalarCertificate = scalar12907 := rfl

noncomputable def tp12908 : ℝ := (583742581 / 2500000000)
noncomputable def tm12908 : ℝ := (-((3051862721 / 5000000000)))
noncomputable def ep12908 : ℝ := (12993124076833121 / 25000000000000000000)
noncomputable def em12908 : ℝ := (25292383983615407 / 50000000000000000000)
noncomputable def bp12908 : ℝ := (2702035116207804873 / 6250000000000000000)
noncomputable def bm12908 : ℝ := (44211500822285277979 / 100000000000000000000)

theorem positive12908 :
    Eplus aL (agent12908.root+dsL) scalar12908.worldRadius world12908.frame
      agent12908.frame tp12908 ≤ -ep12908 := by
  apply positive_check (eT := (1807071851769607679 / 1562500000000000000)) (y := (38004065768046741777 / 100000000000000000000)) (u := (36558601093561078009 / 25000000000000000000))
  · norm_num [world12908, agent12908, scalar12908, tp12908, tm12908, ep12908, em12908, dsL]
  · norm_num [world12908, agent12908, scalar12908, tp12908, tm12908, ep12908, em12908, dsL]
  · norm_num [world12908, agent12908, scalar12908, tp12908, tm12908, ep12908, em12908, dsL]
  · norm_num [world12908, agent12908, scalar12908, tp12908, tm12908, ep12908, em12908, dsL]
  · norm_num [world12908, agent12908, scalar12908, tp12908, tm12908, ep12908, em12908, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12908, agent12908, tp12908, tm12908, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12908, agent12908, scalar12908, tp12908, tm12908, ep12908, em12908, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12908, agent12908, tp12908, tm12908, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12908, agent12908, scalar12908, tp12908, tm12908, ep12908, em12908, dsL]

theorem negative12908 :
    Eminus aL (agent12908.root+dsL) scalar12908.worldRadius world12908.frame
      agent12908.frame tm12908 ≤ -em12908 := by
  apply negative_check (lo := (68376795017374532123 / 100000000000000000000)) (hi := (17094198754343633031 / 25000000000000000000))
    (y := (-((35828000430645118407 / 50000000000000000000)))) (u := (24421478141734297619 / 50000000000000000000))
  · norm_num [world12908, agent12908, scalar12908, tp12908, tm12908, ep12908, em12908, dsL]
  · norm_num [world12908, agent12908, scalar12908, tp12908, tm12908, ep12908, em12908, dsL]
  · norm_num [world12908, agent12908, scalar12908, tp12908, tm12908, ep12908, em12908, dsL]
  · norm_num [world12908, agent12908, scalar12908, tp12908, tm12908, ep12908, em12908, dsL]
  · norm_num [world12908, agent12908, scalar12908, tp12908, tm12908, ep12908, em12908, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12908, agent12908, tp12908, tm12908, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12908, agent12908, tp12908, tm12908, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12908, agent12908, scalar12908, tp12908, tm12908, ep12908, em12908, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12908, agent12908, tp12908, tm12908, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12908, agent12908, scalar12908, tp12908, tm12908, ep12908, em12908, dsL]

theorem tails12908 :
    exp (-((12908:ℝ)*ep12908)) ≤ scalar12908.upperTail ∧
    exp (-((12908:ℝ)*em12908)) ≤ scalar12908.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12908:ℝ)) (by norm_num [ep12908]) ?_)
      (show bp12908^8 ≤ scalar12908.upperTail by norm_num [bp12908, scalar12908])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12908, bp12908, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12908:ℝ)) (by norm_num [em12908]) ?_)
      (show bm12908^8 ≤ scalar12908.lowerTail by norm_num [bm12908, scalar12908])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12908, bm12908, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12908 :
    agent12908.root+dsL+scalar12908.worldRadius < √(1/100/aL) ∧
    2*(agent12908.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12908, agent12908, scalar12908, tp12908, tm12908, ep12908, em12908, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12908, agent12908, scalar12908, tp12908, tm12908, ep12908, em12908, dsL]

noncomputable def master12908 : MasterCertificate 12908 world12908 agent12908 :=
  master scalar12908 dsL tp12908 tm12908 ep12908 em12908
    (by norm_num [dsL]) (by norm_num [tp12908]) (by norm_num [tm12908])
    (by norm_num [ep12908]) (by norm_num [em12908])
    positive12908 negative12908 tails12908.1 tails12908.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12908.1 tailGuards12908.2

theorem preserves12908 : master12908.toScalarCertificate = scalar12908 := rfl

noncomputable def tp12909 : ℝ := (2335048569 / 10000000000)
noncomputable def tm12909 : ℝ := (-((6103892579 / 10000000000)))
noncomputable def ep12909 : ℝ := (51974874039608479 / 100000000000000000000)
noncomputable def em12909 : ℝ := (6323349358840951 / 12500000000000000000)
noncomputable def bp12909 : ℝ := (43228094726724225481 / 100000000000000000000)
noncomputable def bm12909 : ℝ := (690738429394949207 / 1562500000000000000)

theorem positive12909 :
    Eplus aL (agent12909.root+dsL) scalar12909.worldRadius world12909.frame
      agent12909.frame tp12909 ≤ -ep12909 := by
  apply positive_check (eT := (115652800431657977387 / 100000000000000000000)) (y := (19002390987893142703 / 50000000000000000000)) (u := (146235451720116897523 / 100000000000000000000))
  · norm_num [world12909, agent12909, scalar12909, tp12909, tm12909, ep12909, em12909, dsL]
  · norm_num [world12909, agent12909, scalar12909, tp12909, tm12909, ep12909, em12909, dsL]
  · norm_num [world12909, agent12909, scalar12909, tp12909, tm12909, ep12909, em12909, dsL]
  · norm_num [world12909, agent12909, scalar12909, tp12909, tm12909, ep12909, em12909, dsL]
  · norm_num [world12909, agent12909, scalar12909, tp12909, tm12909, ep12909, em12909, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12909, agent12909, tp12909, tm12909, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12909, agent12909, scalar12909, tp12909, tm12909, ep12909, em12909, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12909, agent12909, tp12909, tm12909, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12909, agent12909, scalar12909, tp12909, tm12909, ep12909, em12909, dsL]

theorem negative12909 :
    Eminus aL (agent12909.root+dsL) scalar12909.worldRadius world12909.frame
      agent12909.frame tm12909 ≤ -em12909 := by
  apply negative_check (lo := (17094160553596043319 / 25000000000000000000)) (hi := (68376642214384173277 / 100000000000000000000))
    (y := (-((14331198188986852851 / 20000000000000000000)))) (u := (24421480563455123987 / 50000000000000000000))
  · norm_num [world12909, agent12909, scalar12909, tp12909, tm12909, ep12909, em12909, dsL]
  · norm_num [world12909, agent12909, scalar12909, tp12909, tm12909, ep12909, em12909, dsL]
  · norm_num [world12909, agent12909, scalar12909, tp12909, tm12909, ep12909, em12909, dsL]
  · norm_num [world12909, agent12909, scalar12909, tp12909, tm12909, ep12909, em12909, dsL]
  · norm_num [world12909, agent12909, scalar12909, tp12909, tm12909, ep12909, em12909, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12909, agent12909, tp12909, tm12909, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12909, agent12909, tp12909, tm12909, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12909, agent12909, scalar12909, tp12909, tm12909, ep12909, em12909, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12909, agent12909, tp12909, tm12909, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12909, agent12909, scalar12909, tp12909, tm12909, ep12909, em12909, dsL]

theorem tails12909 :
    exp (-((12909:ℝ)*ep12909)) ≤ scalar12909.upperTail ∧
    exp (-((12909:ℝ)*em12909)) ≤ scalar12909.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12909:ℝ)) (by norm_num [ep12909]) ?_)
      (show bp12909^8 ≤ scalar12909.upperTail by norm_num [bp12909, scalar12909])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12909, bp12909, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12909:ℝ)) (by norm_num [em12909]) ?_)
      (show bm12909^8 ≤ scalar12909.lowerTail by norm_num [bm12909, scalar12909])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12909, bm12909, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12909 :
    agent12909.root+dsL+scalar12909.worldRadius < √(1/100/aL) ∧
    2*(agent12909.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12909, agent12909, scalar12909, tp12909, tm12909, ep12909, em12909, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12909, agent12909, scalar12909, tp12909, tm12909, ep12909, em12909, dsL]

noncomputable def master12909 : MasterCertificate 12909 world12909 agent12909 :=
  master scalar12909 dsL tp12909 tm12909 ep12909 em12909
    (by norm_num [dsL]) (by norm_num [tp12909]) (by norm_num [tm12909])
    (by norm_num [ep12909]) (by norm_num [em12909])
    positive12909 negative12909 tails12909.1 tails12909.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12909.1 tailGuards12909.2

theorem preserves12909 : master12909.toScalarCertificate = scalar12909 := rfl

noncomputable def tp12910 : ℝ := (1167599757 / 5000000000)
noncomputable def tm12910 : ℝ := (-((1526069819 / 2500000000)))
noncomputable def ep12910 : ℝ := (25989314726289901 / 50000000000000000000)
noncomputable def em12910 : ℝ := (50590324605776683 / 100000000000000000000)
noncomputable def bp12910 : ℝ := (21611333423914550277 / 50000000000000000000)
noncomputable def bm12910 : ℝ := (44201946327030880311 / 100000000000000000000)

theorem positive12910 :
    Eplus aL (agent12910.root+dsL) scalar12910.worldRadius world12910.frame
      agent12910.frame tp12910 ≤ -ep12910 := by
  apply positive_check (eT := (14456690750713655643 / 12500000000000000000)) (y := (38004781556812867189 / 100000000000000000000)) (u := (14623545110742922809 / 10000000000000000000))
  · norm_num [world12910, agent12910, scalar12910, tp12910, tm12910, ep12910, em12910, dsL]
  · norm_num [world12910, agent12910, scalar12910, tp12910, tm12910, ep12910, em12910, dsL]
  · norm_num [world12910, agent12910, scalar12910, tp12910, tm12910, ep12910, em12910, dsL]
  · norm_num [world12910, agent12910, scalar12910, tp12910, tm12910, ep12910, em12910, dsL]
  · norm_num [world12910, agent12910, scalar12910, tp12910, tm12910, ep12910, em12910, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12910, agent12910, tp12910, tm12910, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12910, agent12910, scalar12910, tp12910, tm12910, ep12910, em12910, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12910, agent12910, tp12910, tm12910, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12910, agent12910, scalar12910, tp12910, tm12910, ep12910, em12910, dsL]

theorem negative12910 :
    Eminus aL (agent12910.root+dsL) scalar12910.worldRadius world12910.frame
      agent12910.frame tm12910 ≤ -em12910 := by
  apply negative_check (lo := (68375554415665662817 / 100000000000000000000)) (hi := (34187777207832831409 / 50000000000000000000))
    (y := (-((71654097314084200739 / 100000000000000000000)))) (u := (24421943020523716879 / 50000000000000000000))
  · norm_num [world12910, agent12910, scalar12910, tp12910, tm12910, ep12910, em12910, dsL]
  · norm_num [world12910, agent12910, scalar12910, tp12910, tm12910, ep12910, em12910, dsL]
  · norm_num [world12910, agent12910, scalar12910, tp12910, tm12910, ep12910, em12910, dsL]
  · norm_num [world12910, agent12910, scalar12910, tp12910, tm12910, ep12910, em12910, dsL]
  · norm_num [world12910, agent12910, scalar12910, tp12910, tm12910, ep12910, em12910, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12910, agent12910, tp12910, tm12910, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12910, agent12910, tp12910, tm12910, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12910, agent12910, scalar12910, tp12910, tm12910, ep12910, em12910, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12910, agent12910, tp12910, tm12910, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12910, agent12910, scalar12910, tp12910, tm12910, ep12910, em12910, dsL]

theorem tails12910 :
    exp (-((12910:ℝ)*ep12910)) ≤ scalar12910.upperTail ∧
    exp (-((12910:ℝ)*em12910)) ≤ scalar12910.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12910:ℝ)) (by norm_num [ep12910]) ?_)
      (show bp12910^8 ≤ scalar12910.upperTail by norm_num [bp12910, scalar12910])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12910, bp12910, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12910:ℝ)) (by norm_num [em12910]) ?_)
      (show bm12910^8 ≤ scalar12910.lowerTail by norm_num [bm12910, scalar12910])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12910, bm12910, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12910 :
    agent12910.root+dsL+scalar12910.worldRadius < √(1/100/aL) ∧
    2*(agent12910.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12910, agent12910, scalar12910, tp12910, tm12910, ep12910, em12910, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12910, agent12910, scalar12910, tp12910, tm12910, ep12910, em12910, dsL]

noncomputable def master12910 : MasterCertificate 12910 world12910 agent12910 :=
  master scalar12910 dsL tp12910 tm12910 ep12910 em12910
    (by norm_num [dsL]) (by norm_num [tp12910]) (by norm_num [tm12910])
    (by norm_num [ep12910]) (by norm_num [em12910])
    positive12910 negative12910 tails12910.1 tails12910.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12910.1 tailGuards12910.2

theorem preserves12910 : master12910.toScalarCertificate = scalar12910 := rfl

noncomputable def tp12911 : ℝ := (583819449 / 2500000000)
noncomputable def tm12911 : ℝ := (-((6104445941 / 10000000000)))
noncomputable def ep12911 : ℝ := (51981004417217423 / 100000000000000000000)
noncomputable def em12911 : ℝ := (50592348947112331 / 100000000000000000000)
noncomputable def bp12911 : ℝ := (43218202079821033387 / 100000000000000000000)
noncomputable def bm12911 : ℝ := (22098853599621303777 / 50000000000000000000)

theorem positive12911 :
    Eplus aL (agent12911.root+dsL) scalar12911.worldRadius world12911.frame
      agent12911.frame tp12911 ≤ -ep12911 := by
  apply positive_check (eT := (115653728246271531919 / 100000000000000000000)) (y := (1187671847200761947 / 3125000000000000000)) (u := (73118250214477341309 / 50000000000000000000))
  · norm_num [world12911, agent12911, scalar12911, tp12911, tm12911, ep12911, em12911, dsL]
  · norm_num [world12911, agent12911, scalar12911, tp12911, tm12911, ep12911, em12911, dsL]
  · norm_num [world12911, agent12911, scalar12911, tp12911, tm12911, ep12911, em12911, dsL]
  · norm_num [world12911, agent12911, scalar12911, tp12911, tm12911, ep12911, em12911, dsL]
  · norm_num [world12911, agent12911, scalar12911, tp12911, tm12911, ep12911, em12911, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12911, agent12911, tp12911, tm12911, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12911, agent12911, scalar12911, tp12911, tm12911, ep12911, em12911, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12911, agent12911, tp12911, tm12911, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12911, agent12911, scalar12911, tp12911, tm12911, ep12911, em12911, dsL]

theorem negative12911 :
    Eminus aL (agent12911.root+dsL) scalar12911.worldRadius world12911.frame
      agent12911.frame tm12911 ≤ -em12911 := by
  apply negative_check (lo := (34187701765374080443 / 50000000000000000000)) (hi := (68375403530748160887 / 100000000000000000000))
    (y := (-((139949382631703523 / 195312500000000000)))) (u := (48843892589377696031 / 100000000000000000000))
  · norm_num [world12911, agent12911, scalar12911, tp12911, tm12911, ep12911, em12911, dsL]
  · norm_num [world12911, agent12911, scalar12911, tp12911, tm12911, ep12911, em12911, dsL]
  · norm_num [world12911, agent12911, scalar12911, tp12911, tm12911, ep12911, em12911, dsL]
  · norm_num [world12911, agent12911, scalar12911, tp12911, tm12911, ep12911, em12911, dsL]
  · norm_num [world12911, agent12911, scalar12911, tp12911, tm12911, ep12911, em12911, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12911, agent12911, tp12911, tm12911, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12911, agent12911, tp12911, tm12911, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12911, agent12911, scalar12911, tp12911, tm12911, ep12911, em12911, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12911, agent12911, tp12911, tm12911, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12911, agent12911, scalar12911, tp12911, tm12911, ep12911, em12911, dsL]

theorem tails12911 :
    exp (-((12911:ℝ)*ep12911)) ≤ scalar12911.upperTail ∧
    exp (-((12911:ℝ)*em12911)) ≤ scalar12911.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12911:ℝ)) (by norm_num [ep12911]) ?_)
      (show bp12911^8 ≤ scalar12911.upperTail by norm_num [bp12911, scalar12911])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12911, bp12911, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12911:ℝ)) (by norm_num [em12911]) ?_)
      (show bm12911^8 ≤ scalar12911.lowerTail by norm_num [bm12911, scalar12911])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12911, bm12911, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12911 :
    agent12911.root+dsL+scalar12911.worldRadius < √(1/100/aL) ∧
    2*(agent12911.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12911, agent12911, scalar12911, tp12911, tm12911, ep12911, em12911, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12911, agent12911, scalar12911, tp12911, tm12911, ep12911, em12911, dsL]

noncomputable def master12911 : MasterCertificate 12911 world12911 agent12911 :=
  master scalar12911 dsL tp12911 tm12911 ep12911 em12911
    (by norm_num [dsL]) (by norm_num [tp12911]) (by norm_num [tm12911])
    (by norm_num [ep12911]) (by norm_num [em12911])
    positive12911 negative12911 tails12911.1 tails12911.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12911.1 tailGuards12911.2

theorem preserves12911 : master12911.toScalarCertificate = scalar12911 := rfl

noncomputable def tp12912 : ℝ := (1167678021 / 5000000000)
noncomputable def tm12912 : ℝ := (-((1526153139 / 2500000000)))
noncomputable def ep12912 : ℝ := (25991689449483327 / 50000000000000000000)
noncomputable def em12912 : ℝ := (50594372809292349 / 100000000000000000000)
noncomputable def bp12912 : ℝ := (540171723165399999 / 1250000000000000000)
noncomputable def bm12912 : ℝ := (22096734298059422699 / 50000000000000000000)

theorem positive12912 :
    Eplus aL (agent12912.root+dsL) scalar12912.worldRadius world12912.frame
      agent12912.frame tp12912 ≤ -ep12912 := by
  apply positive_check (eT := (115653930260546277549 / 100000000000000000000)) (y := (19003108211822278809 / 50000000000000000000)) (u := (18279693675808400491 / 12500000000000000000))
  · norm_num [world12912, agent12912, scalar12912, tp12912, tm12912, ep12912, em12912, dsL]
  · norm_num [world12912, agent12912, scalar12912, tp12912, tm12912, ep12912, em12912, dsL]
  · norm_num [world12912, agent12912, scalar12912, tp12912, tm12912, ep12912, em12912, dsL]
  · norm_num [world12912, agent12912, scalar12912, tp12912, tm12912, ep12912, em12912, dsL]
  · norm_num [world12912, agent12912, scalar12912, tp12912, tm12912, ep12912, em12912, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12912, agent12912, tp12912, tm12912, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12912, agent12912, scalar12912, tp12912, tm12912, ep12912, em12912, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12912, agent12912, tp12912, tm12912, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12912, agent12912, scalar12912, tp12912, tm12912, ep12912, em12912, dsL]

theorem negative12912 :
    Eminus aL (agent12912.root+dsL) scalar12912.worldRadius world12912.frame
      agent12912.frame tm12912 ≤ -em12912 := by
  apply negative_check (lo := (68375252801671945437 / 100000000000000000000)) (hi := (34187626400835972719 / 50000000000000000000))
    (y := (-((559797429185292307 / 781250000000000000)))) (u := (48843898925268545253 / 100000000000000000000))
  · norm_num [world12912, agent12912, scalar12912, tp12912, tm12912, ep12912, em12912, dsL]
  · norm_num [world12912, agent12912, scalar12912, tp12912, tm12912, ep12912, em12912, dsL]
  · norm_num [world12912, agent12912, scalar12912, tp12912, tm12912, ep12912, em12912, dsL]
  · norm_num [world12912, agent12912, scalar12912, tp12912, tm12912, ep12912, em12912, dsL]
  · norm_num [world12912, agent12912, scalar12912, tp12912, tm12912, ep12912, em12912, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12912, agent12912, tp12912, tm12912, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12912, agent12912, tp12912, tm12912, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12912, agent12912, scalar12912, tp12912, tm12912, ep12912, em12912, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12912, agent12912, tp12912, tm12912, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12912, agent12912, scalar12912, tp12912, tm12912, ep12912, em12912, dsL]

theorem tails12912 :
    exp (-((12912:ℝ)*ep12912)) ≤ scalar12912.upperTail ∧
    exp (-((12912:ℝ)*em12912)) ≤ scalar12912.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12912:ℝ)) (by norm_num [ep12912]) ?_)
      (show bp12912^8 ≤ scalar12912.upperTail by norm_num [bp12912, scalar12912])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12912, bp12912, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12912:ℝ)) (by norm_num [em12912]) ?_)
      (show bm12912^8 ≤ scalar12912.lowerTail by norm_num [bm12912, scalar12912])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12912, bm12912, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12912 :
    agent12912.root+dsL+scalar12912.worldRadius < √(1/100/aL) ∧
    2*(agent12912.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12912, agent12912, scalar12912, tp12912, tm12912, ep12912, em12912, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12912, agent12912, scalar12912, tp12912, tm12912, ep12912, em12912, dsL]

noncomputable def master12912 : MasterCertificate 12912 world12912 agent12912 :=
  master scalar12912 dsL tp12912 tm12912 ep12912 em12912
    (by norm_num [dsL]) (by norm_num [tp12912]) (by norm_num [tm12912])
    (by norm_num [ep12912]) (by norm_num [em12912])
    positive12912 negative12912 tails12912.1 tails12912.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12912.1 tailGuards12912.2

theorem preserves12912 : master12912.toScalarCertificate = scalar12912 := rfl

noncomputable def tp12913 : ℝ := (93417369 / 400000000)
noncomputable def tm12913 : ℝ := (-((3052389547 / 5000000000)))
noncomputable def ep12913 : ℝ := (25992875813652363 / 50000000000000000000)
noncomputable def em12913 : ℝ := (50596395094461957 / 100000000000000000000)
noncomputable def bp12913 : ℝ := (8641855010839202989 / 20000000000000000000)
noncomputable def bm12913 : ℝ := (44189231300732268523 / 100000000000000000000)

theorem positive12913 :
    Eplus aL (agent12913.root+dsL) scalar12913.worldRadius world12913.frame
      agent12913.frame tp12913 ≤ -ep12913 := by
  apply positive_check (eT := (11565413185407097567 / 10000000000000000000)) (y := (7601386563279214109 / 20000000000000000000)) (u := (9139912315338983893 / 6250000000000000000))
  · norm_num [world12913, agent12913, scalar12913, tp12913, tm12913, ep12913, em12913, dsL]
  · norm_num [world12913, agent12913, scalar12913, tp12913, tm12913, ep12913, em12913, dsL]
  · norm_num [world12913, agent12913, scalar12913, tp12913, tm12913, ep12913, em12913, dsL]
  · norm_num [world12913, agent12913, scalar12913, tp12913, tm12913, ep12913, em12913, dsL]
  · norm_num [world12913, agent12913, scalar12913, tp12913, tm12913, ep12913, em12913, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12913, agent12913, tp12913, tm12913, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12913, agent12913, scalar12913, tp12913, tm12913, ep12913, em12913, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12913, agent12913, tp12913, tm12913, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12913, agent12913, scalar12913, tp12913, tm12913, ep12913, em12913, dsL]

theorem negative12913 :
    Eminus aL (agent12913.root+dsL) scalar12913.worldRadius world12913.frame
      agent12913.frame tm12913 ≤ -em12913 := by
  apply negative_check (lo := (34187551171710134353 / 50000000000000000000)) (hi := (68375102343420268707 / 100000000000000000000))
    (y := (-((71654057302215622389 / 100000000000000000000)))) (u := (12210976396100708723 / 25000000000000000000))
  · norm_num [world12913, agent12913, scalar12913, tp12913, tm12913, ep12913, em12913, dsL]
  · norm_num [world12913, agent12913, scalar12913, tp12913, tm12913, ep12913, em12913, dsL]
  · norm_num [world12913, agent12913, scalar12913, tp12913, tm12913, ep12913, em12913, dsL]
  · norm_num [world12913, agent12913, scalar12913, tp12913, tm12913, ep12913, em12913, dsL]
  · norm_num [world12913, agent12913, scalar12913, tp12913, tm12913, ep12913, em12913, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12913, agent12913, tp12913, tm12913, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12913, agent12913, tp12913, tm12913, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12913, agent12913, scalar12913, tp12913, tm12913, ep12913, em12913, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12913, agent12913, tp12913, tm12913, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12913, agent12913, scalar12913, tp12913, tm12913, ep12913, em12913, dsL]

theorem tails12913 :
    exp (-((12913:ℝ)*ep12913)) ≤ scalar12913.upperTail ∧
    exp (-((12913:ℝ)*em12913)) ≤ scalar12913.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12913:ℝ)) (by norm_num [ep12913]) ?_)
      (show bp12913^8 ≤ scalar12913.upperTail by norm_num [bp12913, scalar12913])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12913, bp12913, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12913:ℝ)) (by norm_num [em12913]) ?_)
      (show bm12913^8 ≤ scalar12913.lowerTail by norm_num [bm12913, scalar12913])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12913, bm12913, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12913 :
    agent12913.root+dsL+scalar12913.worldRadius < √(1/100/aL) ∧
    2*(agent12913.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12913, agent12913, scalar12913, tp12913, tm12913, ep12913, em12913, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12913, agent12913, scalar12913, tp12913, tm12913, ep12913, em12913, dsL]

noncomputable def master12913 : MasterCertificate 12913 world12913 agent12913 :=
  master scalar12913 dsL tp12913 tm12913 ep12913 em12913
    (by norm_num [dsL]) (by norm_num [tp12913]) (by norm_num [tm12913])
    (by norm_num [ep12913]) (by norm_num [em12913])
    positive12913 negative12913 tails12913.1 tails12913.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12913.1 tailGuards12913.2

theorem preserves12913 : master12913.toScalarCertificate = scalar12913 := rfl

noncomputable def tp12914 : ℝ := (2335512377 / 10000000000)
noncomputable def tm12914 : ℝ := (-((3052472807 / 5000000000)))
noncomputable def ep12914 : ℝ := (12997030931215127 / 25000000000000000000)
noncomputable def em12914 : ℝ := (50598416747024519 / 100000000000000000000)
noncomputable def bp12914 : ℝ := (2160240644984545563 / 5000000000000000000)
noncomputable def bm12914 : ℝ := (44184994639444326289 / 100000000000000000000)

theorem positive12914 :
    Eplus aL (agent12914.root+dsL) scalar12914.worldRadius world12914.frame
      agent12914.frame tp12914 ≤ -ep12914 := by
  apply positive_check (eT := (57827166628643535633 / 50000000000000000000)) (y := (38007649208130842469 / 100000000000000000000)) (u := (146239644690398638647 / 100000000000000000000))
  · norm_num [world12914, agent12914, scalar12914, tp12914, tm12914, ep12914, em12914, dsL]
  · norm_num [world12914, agent12914, scalar12914, tp12914, tm12914, ep12914, em12914, dsL]
  · norm_num [world12914, agent12914, scalar12914, tp12914, tm12914, ep12914, em12914, dsL]
  · norm_num [world12914, agent12914, scalar12914, tp12914, tm12914, ep12914, em12914, dsL]
  · norm_num [world12914, agent12914, scalar12914, tp12914, tm12914, ep12914, em12914, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12914, agent12914, tp12914, tm12914, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12914, agent12914, scalar12914, tp12914, tm12914, ep12914, em12914, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12914, agent12914, tp12914, tm12914, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12914, agent12914, scalar12914, tp12914, tm12914, ep12914, em12914, dsL]

theorem negative12914 :
    Eminus aL (agent12914.root+dsL) scalar12914.worldRadius world12914.frame
      agent12914.frame tm12914 ≤ -em12914 := by
  apply negative_check (lo := (13674990380967197157 / 20000000000000000000)) (hi := (34187475952417992893 / 50000000000000000000))
    (y := (-((3582702234938361667 / 5000000000000000000)))) (u := (48843911740419654353 / 100000000000000000000))
  · norm_num [world12914, agent12914, scalar12914, tp12914, tm12914, ep12914, em12914, dsL]
  · norm_num [world12914, agent12914, scalar12914, tp12914, tm12914, ep12914, em12914, dsL]
  · norm_num [world12914, agent12914, scalar12914, tp12914, tm12914, ep12914, em12914, dsL]
  · norm_num [world12914, agent12914, scalar12914, tp12914, tm12914, ep12914, em12914, dsL]
  · norm_num [world12914, agent12914, scalar12914, tp12914, tm12914, ep12914, em12914, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12914, agent12914, tp12914, tm12914, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12914, agent12914, tp12914, tm12914, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12914, agent12914, scalar12914, tp12914, tm12914, ep12914, em12914, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12914, agent12914, tp12914, tm12914, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12914, agent12914, scalar12914, tp12914, tm12914, ep12914, em12914, dsL]

theorem tails12914 :
    exp (-((12914:ℝ)*ep12914)) ≤ scalar12914.upperTail ∧
    exp (-((12914:ℝ)*em12914)) ≤ scalar12914.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12914:ℝ)) (by norm_num [ep12914]) ?_)
      (show bp12914^8 ≤ scalar12914.upperTail by norm_num [bp12914, scalar12914])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12914, bp12914, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12914:ℝ)) (by norm_num [em12914]) ?_)
      (show bm12914^8 ≤ scalar12914.lowerTail by norm_num [bm12914, scalar12914])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12914, bm12914, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12914 :
    agent12914.root+dsL+scalar12914.worldRadius < √(1/100/aL) ∧
    2*(agent12914.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12914, agent12914, scalar12914, tp12914, tm12914, ep12914, em12914, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12914, agent12914, scalar12914, tp12914, tm12914, ep12914, em12914, dsL]

noncomputable def master12914 : MasterCertificate 12914 world12914 agent12914 :=
  master scalar12914 dsL tp12914 tm12914 ep12914 em12914
    (by norm_num [dsL]) (by norm_num [tp12914]) (by norm_num [tm12914])
    (by norm_num [ep12914]) (by norm_num [em12914])
    positive12914 negative12914 tails12914.1 tails12914.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12914.1 tailGuards12914.2

theorem preserves12914 : master12914.toScalarCertificate = scalar12914 := rfl

noncomputable def tp12915 : ℝ := (1167795223 / 5000000000)
noncomputable def tm12915 : ℝ := (-((610511213 / 1000000000)))
noncomputable def ep12915 : ℝ := (51990494410671683 / 100000000000000000000)
noncomputable def em12915 : ℝ := (50600437121492917 / 100000000000000000000)
noncomputable def bp12915 : ℝ := (43200351934369748309 / 100000000000000000000)
noncomputable def bm12915 : ℝ := (11045189768161148787 / 25000000000000000000)

theorem positive12915 :
    Eplus aL (agent12915.root+dsL) scalar12915.worldRadius world12915.frame
      agent12915.frame tp12915 ≤ -ep12915 := by
  apply positive_check (eT := (115654534095773191009 / 100000000000000000000)) (y := (19004182216221272571 / 50000000000000000000)) (u := (73120345317815617411 / 50000000000000000000))
  · norm_num [world12915, agent12915, scalar12915, tp12915, tm12915, ep12915, em12915, dsL]
  · norm_num [world12915, agent12915, scalar12915, tp12915, tm12915, ep12915, em12915, dsL]
  · norm_num [world12915, agent12915, scalar12915, tp12915, tm12915, ep12915, em12915, dsL]
  · norm_num [world12915, agent12915, scalar12915, tp12915, tm12915, ep12915, em12915, dsL]
  · norm_num [world12915, agent12915, scalar12915, tp12915, tm12915, ep12915, em12915, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12915, agent12915, tp12915, tm12915, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12915, agent12915, scalar12915, tp12915, tm12915, ep12915, em12915, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12915, agent12915, tp12915, tm12915, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12915, agent12915, scalar12915, tp12915, tm12915, ep12915, em12915, dsL]

theorem negative12915 :
    Eminus aL (agent12915.root+dsL) scalar12915.worldRadius world12915.frame
      agent12915.frame tm12915 ≤ -em12915 := by
  apply negative_check (lo := (3418740071310774733 / 5000000000000000000)) (hi := (68374801426215494661 / 100000000000000000000))
    (y := (-((71654032552070513673 / 100000000000000000000)))) (u := (48843917673341839811 / 100000000000000000000))
  · norm_num [world12915, agent12915, scalar12915, tp12915, tm12915, ep12915, em12915, dsL]
  · norm_num [world12915, agent12915, scalar12915, tp12915, tm12915, ep12915, em12915, dsL]
  · norm_num [world12915, agent12915, scalar12915, tp12915, tm12915, ep12915, em12915, dsL]
  · norm_num [world12915, agent12915, scalar12915, tp12915, tm12915, ep12915, em12915, dsL]
  · norm_num [world12915, agent12915, scalar12915, tp12915, tm12915, ep12915, em12915, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12915, agent12915, tp12915, tm12915, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12915, agent12915, tp12915, tm12915, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12915, agent12915, scalar12915, tp12915, tm12915, ep12915, em12915, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12915, agent12915, tp12915, tm12915, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12915, agent12915, scalar12915, tp12915, tm12915, ep12915, em12915, dsL]

theorem tails12915 :
    exp (-((12915:ℝ)*ep12915)) ≤ scalar12915.upperTail ∧
    exp (-((12915:ℝ)*em12915)) ≤ scalar12915.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12915:ℝ)) (by norm_num [ep12915]) ?_)
      (show bp12915^8 ≤ scalar12915.upperTail by norm_num [bp12915, scalar12915])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12915, bp12915, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12915:ℝ)) (by norm_num [em12915]) ?_)
      (show bm12915^8 ≤ scalar12915.lowerTail by norm_num [bm12915, scalar12915])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12915, bm12915, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12915 :
    agent12915.root+dsL+scalar12915.worldRadius < √(1/100/aL) ∧
    2*(agent12915.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12915, agent12915, scalar12915, tp12915, tm12915, ep12915, em12915, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12915, agent12915, scalar12915, tp12915, tm12915, ep12915, em12915, dsL]

noncomputable def master12915 : MasterCertificate 12915 world12915 agent12915 :=
  master scalar12915 dsL tp12915 tm12915 ep12915 em12915
    (by norm_num [dsL]) (by norm_num [tp12915]) (by norm_num [tm12915])
    (by norm_num [ep12915]) (by norm_num [em12915])
    positive12915 negative12915 tails12915.1 tails12915.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12915.1 tailGuards12915.2

theorem preserves12915 : master12915.toScalarCertificate = scalar12915 := rfl

noncomputable def tp12916 : ℝ := (583917133 / 2500000000)
noncomputable def tm12916 : ℝ := (-((3052639159 / 5000000000)))
noncomputable def ep12916 : ℝ := (5199286380123477 / 10000000000000000000)
noncomputable def em12916 : ℝ := (5060245628181517 / 10000000000000000000)
noncomputable def bp12916 : ℝ := (10798973019235899641 / 25000000000000000000)
noncomputable def bm12916 : ℝ := (4417652455469827799 / 10000000000000000000)

theorem positive12916 :
    Eplus aL (agent12916.root+dsL) scalar12916.worldRadius world12916.frame
      agent12916.frame tp12916 ≤ -ep12916 := by
  apply positive_check (eT := (115654735089711114167 / 100000000000000000000)) (y := (1187783759027339749 / 3125000000000000000)) (u := (36560434378192223339 / 25000000000000000000))
  · norm_num [world12916, agent12916, scalar12916, tp12916, tm12916, ep12916, em12916, dsL]
  · norm_num [world12916, agent12916, scalar12916, tp12916, tm12916, ep12916, em12916, dsL]
  · norm_num [world12916, agent12916, scalar12916, tp12916, tm12916, ep12916, em12916, dsL]
  · norm_num [world12916, agent12916, scalar12916, tp12916, tm12916, ep12916, em12916, dsL]
  · norm_num [world12916, agent12916, scalar12916, tp12916, tm12916, ep12916, em12916, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12916, agent12916, tp12916, tm12916, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12916, agent12916, scalar12916, tp12916, tm12916, ep12916, em12916, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12916, agent12916, tp12916, tm12916, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12916, agent12916, scalar12916, tp12916, tm12916, ep12916, em12916, dsL]

theorem negative12916 :
    Eminus aL (agent12916.root+dsL) scalar12916.worldRadius world12916.frame
      agent12916.frame tm12916 ≤ -em12916 := by
  apply negative_check (lo := (34187326143528050981 / 50000000000000000000)) (hi := (68374652287056101963 / 100000000000000000000))
    (y := (-((71654017614728870353 / 100000000000000000000)))) (u := (48843924969325239573 / 100000000000000000000))
  · norm_num [world12916, agent12916, scalar12916, tp12916, tm12916, ep12916, em12916, dsL]
  · norm_num [world12916, agent12916, scalar12916, tp12916, tm12916, ep12916, em12916, dsL]
  · norm_num [world12916, agent12916, scalar12916, tp12916, tm12916, ep12916, em12916, dsL]
  · norm_num [world12916, agent12916, scalar12916, tp12916, tm12916, ep12916, em12916, dsL]
  · norm_num [world12916, agent12916, scalar12916, tp12916, tm12916, ep12916, em12916, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12916, agent12916, tp12916, tm12916, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12916, agent12916, tp12916, tm12916, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12916, agent12916, scalar12916, tp12916, tm12916, ep12916, em12916, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12916, agent12916, tp12916, tm12916, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12916, agent12916, scalar12916, tp12916, tm12916, ep12916, em12916, dsL]

theorem tails12916 :
    exp (-((12916:ℝ)*ep12916)) ≤ scalar12916.upperTail ∧
    exp (-((12916:ℝ)*em12916)) ≤ scalar12916.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12916:ℝ)) (by norm_num [ep12916]) ?_)
      (show bp12916^8 ≤ scalar12916.upperTail by norm_num [bp12916, scalar12916])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12916, bp12916, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12916:ℝ)) (by norm_num [em12916]) ?_)
      (show bm12916^8 ≤ scalar12916.lowerTail by norm_num [bm12916, scalar12916])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12916, bm12916, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12916 :
    agent12916.root+dsL+scalar12916.worldRadius < √(1/100/aL) ∧
    2*(agent12916.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12916, agent12916, scalar12916, tp12916, tm12916, ep12916, em12916, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12916, agent12916, scalar12916, tp12916, tm12916, ep12916, em12916, dsL]

noncomputable def master12916 : MasterCertificate 12916 world12916 agent12916 :=
  master scalar12916 dsL tp12916 tm12916 ep12916 em12916
    (by norm_num [dsL]) (by norm_num [tp12916]) (by norm_num [tm12916])
    (by norm_num [ep12916]) (by norm_num [em12916])
    positive12916 negative12916 tails12916.1 tails12916.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12916.1 tailGuards12916.2

theorem preserves12916 : master12916.toScalarCertificate = scalar12916 := rfl

noncomputable def tp12917 : ℝ := (2335746567 / 10000000000)
noncomputable def tm12917 : ℝ := (-((610544471 / 1000000000)))
noncomputable def ep12917 : ℝ := (51995232103015649 / 100000000000000000000)
noncomputable def em12917 : ℝ := (50604474447026109 / 100000000000000000000)
noncomputable def bp12917 : ℝ := (21595716591694555257 / 50000000000000000000)
noncomputable def bm12917 : ℝ := (22086145464681700913 / 50000000000000000000)

theorem positive12917 :
    Eplus aL (agent12917.root+dsL) scalar12917.worldRadius world12917.frame
      agent12917.frame tp12917 ≤ -ep12917 := by
  apply positive_check (eT := (3614216742166912389 / 3125000000000000000)) (y := (19004897820049759097 / 50000000000000000000)) (u := (146242783658570938809 / 100000000000000000000))
  · norm_num [world12917, agent12917, scalar12917, tp12917, tm12917, ep12917, em12917, dsL]
  · norm_num [world12917, agent12917, scalar12917, tp12917, tm12917, ep12917, em12917, dsL]
  · norm_num [world12917, agent12917, scalar12917, tp12917, tm12917, ep12917, em12917, dsL]
  · norm_num [world12917, agent12917, scalar12917, tp12917, tm12917, ep12917, em12917, dsL]
  · norm_num [world12917, agent12917, scalar12917, tp12917, tm12917, ep12917, em12917, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12917, agent12917, tp12917, tm12917, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12917, agent12917, scalar12917, tp12917, tm12917, ep12917, em12917, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12917, agent12917, tp12917, tm12917, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12917, agent12917, scalar12917, tp12917, tm12917, ep12917, em12917, dsL]

theorem negative12917 :
    Eminus aL (agent12917.root+dsL) scalar12917.worldRadius world12917.frame
      agent12917.frame tm12917 ≤ -em12917 := by
  apply negative_check (lo := (68374502222343778893 / 100000000000000000000)) (hi := (34187251111171889447 / 50000000000000000000))
    (y := (-((4478375347177715413 / 6250000000000000000)))) (u := (48843930859846982529 / 100000000000000000000))
  · norm_num [world12917, agent12917, scalar12917, tp12917, tm12917, ep12917, em12917, dsL]
  · norm_num [world12917, agent12917, scalar12917, tp12917, tm12917, ep12917, em12917, dsL]
  · norm_num [world12917, agent12917, scalar12917, tp12917, tm12917, ep12917, em12917, dsL]
  · norm_num [world12917, agent12917, scalar12917, tp12917, tm12917, ep12917, em12917, dsL]
  · norm_num [world12917, agent12917, scalar12917, tp12917, tm12917, ep12917, em12917, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12917, agent12917, tp12917, tm12917, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12917, agent12917, tp12917, tm12917, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12917, agent12917, scalar12917, tp12917, tm12917, ep12917, em12917, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12917, agent12917, tp12917, tm12917, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12917, agent12917, scalar12917, tp12917, tm12917, ep12917, em12917, dsL]

theorem tails12917 :
    exp (-((12917:ℝ)*ep12917)) ≤ scalar12917.upperTail ∧
    exp (-((12917:ℝ)*em12917)) ≤ scalar12917.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12917:ℝ)) (by norm_num [ep12917]) ?_)
      (show bp12917^8 ≤ scalar12917.upperTail by norm_num [bp12917, scalar12917])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12917, bp12917, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12917:ℝ)) (by norm_num [em12917]) ?_)
      (show bm12917^8 ≤ scalar12917.lowerTail by norm_num [bm12917, scalar12917])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12917, bm12917, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12917 :
    agent12917.root+dsL+scalar12917.worldRadius < √(1/100/aL) ∧
    2*(agent12917.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12917, agent12917, scalar12917, tp12917, tm12917, ep12917, em12917, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12917, agent12917, scalar12917, tp12917, tm12917, ep12917, em12917, dsL]

noncomputable def master12917 : MasterCertificate 12917 world12917 agent12917 :=
  master scalar12917 dsL tp12917 tm12917 ep12917 em12917
    (by norm_num [dsL]) (by norm_num [tp12917]) (by norm_num [tm12917])
    (by norm_num [ep12917]) (by norm_num [em12917])
    positive12917 negative12917 tails12917.1 tails12917.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12917.1 tailGuards12917.2

theorem preserves12917 : master12917.toScalarCertificate = scalar12917 := rfl

noncomputable def tp12918 : ℝ := (1167912281 / 5000000000)
noncomputable def tm12918 : ℝ := (-((76320133 / 125000000)))
noncomputable def ep12918 : ℝ := (51997599119005187 / 100000000000000000000)
noncomputable def em12918 : ℝ := (50606491406205429 / 100000000000000000000)
noncomputable def bp12918 : ℝ := (5398371923883224507 / 12500000000000000000)
noncomputable def bm12918 : ℝ := (22084029173527545527 / 50000000000000000000)

theorem positive12918 :
    Eplus aL (agent12918.root+dsL) scalar12918.worldRadius world12918.frame
      agent12918.frame tp12918 ≤ -ep12918 := by
  apply positive_check (eT := (1807111502404786769 / 1562500000000000000)) (y := (7602102125312072993 / 20000000000000000000)) (u := (146243829278412078719 / 100000000000000000000))
  · norm_num [world12918, agent12918, scalar12918, tp12918, tm12918, ep12918, em12918, dsL]
  · norm_num [world12918, agent12918, scalar12918, tp12918, tm12918, ep12918, em12918, dsL]
  · norm_num [world12918, agent12918, scalar12918, tp12918, tm12918, ep12918, em12918, dsL]
  · norm_num [world12918, agent12918, scalar12918, tp12918, tm12918, ep12918, em12918, dsL]
  · norm_num [world12918, agent12918, scalar12918, tp12918, tm12918, ep12918, em12918, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12918, agent12918, tp12918, tm12918, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12918, agent12918, scalar12918, tp12918, tm12918, ep12918, em12918, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12918, agent12918, tp12918, tm12918, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12918, agent12918, scalar12918, tp12918, tm12918, ep12918, em12918, dsL]

theorem negative12918 :
    Eminus aL (agent12918.root+dsL) scalar12918.worldRadius world12918.frame
      agent12918.frame tm12918 ≤ -em12918 := by
  apply negative_check (lo := (68374354067563245713 / 100000000000000000000)) (hi := (34187177033781622857 / 50000000000000000000))
    (y := (-((7165398941153600991 / 10000000000000000000)))) (u := (24421969372436770927 / 50000000000000000000))
  · norm_num [world12918, agent12918, scalar12918, tp12918, tm12918, ep12918, em12918, dsL]
  · norm_num [world12918, agent12918, scalar12918, tp12918, tm12918, ep12918, em12918, dsL]
  · norm_num [world12918, agent12918, scalar12918, tp12918, tm12918, ep12918, em12918, dsL]
  · norm_num [world12918, agent12918, scalar12918, tp12918, tm12918, ep12918, em12918, dsL]
  · norm_num [world12918, agent12918, scalar12918, tp12918, tm12918, ep12918, em12918, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12918, agent12918, tp12918, tm12918, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12918, agent12918, tp12918, tm12918, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12918, agent12918, scalar12918, tp12918, tm12918, ep12918, em12918, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12918, agent12918, tp12918, tm12918, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12918, agent12918, scalar12918, tp12918, tm12918, ep12918, em12918, dsL]

theorem tails12918 :
    exp (-((12918:ℝ)*ep12918)) ≤ scalar12918.upperTail ∧
    exp (-((12918:ℝ)*em12918)) ≤ scalar12918.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12918:ℝ)) (by norm_num [ep12918]) ?_)
      (show bp12918^8 ≤ scalar12918.upperTail by norm_num [bp12918, scalar12918])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12918, bp12918, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12918:ℝ)) (by norm_num [em12918]) ?_)
      (show bm12918^8 ≤ scalar12918.lowerTail by norm_num [bm12918, scalar12918])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12918, bm12918, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12918 :
    agent12918.root+dsL+scalar12918.worldRadius < √(1/100/aL) ∧
    2*(agent12918.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12918, agent12918, scalar12918, tp12918, tm12918, ep12918, em12918, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12918, agent12918, scalar12918, tp12918, tm12918, ep12918, em12918, dsL]

noncomputable def master12918 : MasterCertificate 12918 world12918 agent12918 :=
  master scalar12918 dsL tp12918 tm12918 ep12918 em12918
    (by norm_num [dsL]) (by norm_num [tp12918]) (by norm_num [tm12918])
    (by norm_num [ep12918]) (by norm_num [em12918])
    positive12918 negative12918 tails12918.1 tails12918.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12918.1 tailGuards12918.2

theorem preserves12918 : master12918.toScalarCertificate = scalar12918 := rfl

noncomputable def tp12919 : ℝ := (36498477 / 156250000)
noncomputable def tm12919 : ℝ := (-((6105776801 / 10000000000)))
noncomputable def ep12919 : ℝ := (25999982359318499 / 50000000000000000000)
noncomputable def em12919 : ℝ := (6326063385437593 / 12500000000000000000)
noncomputable def bp12919 : ℝ := (53978148488731929 / 125000000000000000)
noncomputable def bm12919 : ℝ := (44163826861848209883 / 100000000000000000000)

theorem positive12919 :
    Eplus aL (agent12919.root+dsL) scalar12919.worldRadius world12919.frame
      agent12919.frame tp12919 ≤ -ep12919 := by
  apply positive_check (eT := (115655336382643239359 / 100000000000000000000)) (y := (950280634732698761 / 2500000000000000000)) (u := (18280609322320013361 / 12500000000000000000))
  · norm_num [world12919, agent12919, scalar12919, tp12919, tm12919, ep12919, em12919, dsL]
  · norm_num [world12919, agent12919, scalar12919, tp12919, tm12919, ep12919, em12919, dsL]
  · norm_num [world12919, agent12919, scalar12919, tp12919, tm12919, ep12919, em12919, dsL]
  · norm_num [world12919, agent12919, scalar12919, tp12919, tm12919, ep12919, em12919, dsL]
  · norm_num [world12919, agent12919, scalar12919, tp12919, tm12919, ep12919, em12919, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12919, agent12919, tp12919, tm12919, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12919, agent12919, scalar12919, tp12919, tm12919, ep12919, em12919, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12919, agent12919, tp12919, tm12919, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12919, agent12919, scalar12919, tp12919, tm12919, ep12919, em12919, dsL]

theorem negative12919 :
    Eminus aL (agent12919.root+dsL) scalar12919.worldRadius world12919.frame
      agent12919.frame tm12919 ≤ -em12919 := by
  apply negative_check (lo := (17093551218064545613 / 25000000000000000000)) (hi := (68374204872258182453 / 100000000000000000000))
    (y := (-((17913493997694725981 / 25000000000000000000)))) (u := (610549316251254521 / 1250000000000000000))
  · norm_num [world12919, agent12919, scalar12919, tp12919, tm12919, ep12919, em12919, dsL]
  · norm_num [world12919, agent12919, scalar12919, tp12919, tm12919, ep12919, em12919, dsL]
  · norm_num [world12919, agent12919, scalar12919, tp12919, tm12919, ep12919, em12919, dsL]
  · norm_num [world12919, agent12919, scalar12919, tp12919, tm12919, ep12919, em12919, dsL]
  · norm_num [world12919, agent12919, scalar12919, tp12919, tm12919, ep12919, em12919, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12919, agent12919, tp12919, tm12919, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12919, agent12919, tp12919, tm12919, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12919, agent12919, scalar12919, tp12919, tm12919, ep12919, em12919, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12919, agent12919, tp12919, tm12919, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12919, agent12919, scalar12919, tp12919, tm12919, ep12919, em12919, dsL]

theorem tails12919 :
    exp (-((12919:ℝ)*ep12919)) ≤ scalar12919.upperTail ∧
    exp (-((12919:ℝ)*em12919)) ≤ scalar12919.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12919:ℝ)) (by norm_num [ep12919]) ?_)
      (show bp12919^8 ≤ scalar12919.upperTail by norm_num [bp12919, scalar12919])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12919, bp12919, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12919:ℝ)) (by norm_num [em12919]) ?_)
      (show bm12919^8 ≤ scalar12919.lowerTail by norm_num [bm12919, scalar12919])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12919, bm12919, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12919 :
    agent12919.root+dsL+scalar12919.worldRadius < √(1/100/aL) ∧
    2*(agent12919.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12919, agent12919, scalar12919, tp12919, tm12919, ep12919, em12919, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12919, agent12919, scalar12919, tp12919, tm12919, ep12919, em12919, dsL]

noncomputable def master12919 : MasterCertificate 12919 world12919 agent12919 :=
  master scalar12919 dsL tp12919 tm12919 ep12919 em12919
    (by norm_num [dsL]) (by norm_num [tp12919]) (by norm_num [tm12919])
    (by norm_num [ep12919]) (by norm_num [em12919])
    positive12919 negative12919 tails12919.1 tails12919.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12919.1 tailGuards12919.2

theorem preserves12919 : master12919.toScalarCertificate = scalar12919 := rfl

noncomputable def tp12920 : ℝ := (146003309 / 625000000)
noncomputable def tm12920 : ℝ := (-((3053081059 / 5000000000)))
noncomputable def ep12920 : ℝ := (26001852926299377 / 50000000000000000000)
noncomputable def em12920 : ℝ := (50612023338216367 / 100000000000000000000)
noncomputable def bp12920 : ℝ := (10794275802661231269 / 25000000000000000000)
noncomputable def bm12920 : ℝ := (5519815674308556749 / 12500000000000000000)

theorem positive12920 :
    Eplus aL (agent12920.root+dsL) scalar12920.worldRadius world12920.frame
      agent12920.frame tp12920 ≤ -ep12920 := by
  apply positive_check (eT := (115656058365732944251 / 100000000000000000000)) (y := (1187850661161890669 / 3125000000000000000)) (u := (29248973677858151603 / 20000000000000000000))
  · norm_num [world12920, agent12920, scalar12920, tp12920, tm12920, ep12920, em12920, dsL]
  · norm_num [world12920, agent12920, scalar12920, tp12920, tm12920, ep12920, em12920, dsL]
  · norm_num [world12920, agent12920, scalar12920, tp12920, tm12920, ep12920, em12920, dsL]
  · norm_num [world12920, agent12920, scalar12920, tp12920, tm12920, ep12920, em12920, dsL]
  · norm_num [world12920, agent12920, scalar12920, tp12920, tm12920, ep12920, em12920, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12920, agent12920, tp12920, tm12920, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12920, agent12920, scalar12920, tp12920, tm12920, ep12920, em12920, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12920, agent12920, tp12920, tm12920, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12920, agent12920, scalar12920, tp12920, tm12920, ep12920, em12920, dsL]

theorem negative12920 :
    Eminus aL (agent12920.root+dsL) scalar12920.worldRadius world12920.frame
      agent12920.frame tm12920 ≤ -em12920 := by
  apply negative_check (lo := (2734924905406724841 / 4000000000000000000)) (hi := (34186561317584060513 / 50000000000000000000))
    (y := (-((17913019738988918167 / 25000000000000000000)))) (u := (48844871895540635909 / 100000000000000000000))
  · norm_num [world12920, agent12920, scalar12920, tp12920, tm12920, ep12920, em12920, dsL]
  · norm_num [world12920, agent12920, scalar12920, tp12920, tm12920, ep12920, em12920, dsL]
  · norm_num [world12920, agent12920, scalar12920, tp12920, tm12920, ep12920, em12920, dsL]
  · norm_num [world12920, agent12920, scalar12920, tp12920, tm12920, ep12920, em12920, dsL]
  · norm_num [world12920, agent12920, scalar12920, tp12920, tm12920, ep12920, em12920, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12920, agent12920, tp12920, tm12920, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12920, agent12920, tp12920, tm12920, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12920, agent12920, scalar12920, tp12920, tm12920, ep12920, em12920, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12920, agent12920, tp12920, tm12920, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12920, agent12920, scalar12920, tp12920, tm12920, ep12920, em12920, dsL]

theorem tails12920 :
    exp (-((12920:ℝ)*ep12920)) ≤ scalar12920.upperTail ∧
    exp (-((12920:ℝ)*em12920)) ≤ scalar12920.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12920:ℝ)) (by norm_num [ep12920]) ?_)
      (show bp12920^8 ≤ scalar12920.upperTail by norm_num [bp12920, scalar12920])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12920, bp12920, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12920:ℝ)) (by norm_num [em12920]) ?_)
      (show bm12920^8 ≤ scalar12920.lowerTail by norm_num [bm12920, scalar12920])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12920, bm12920, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12920 :
    agent12920.root+dsL+scalar12920.worldRadius < √(1/100/aL) ∧
    2*(agent12920.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12920, agent12920, scalar12920, tp12920, tm12920, ep12920, em12920, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12920, agent12920, scalar12920, tp12920, tm12920, ep12920, em12920, dsL]

noncomputable def master12920 : MasterCertificate 12920 world12920 agent12920 :=
  master scalar12920 dsL tp12920 tm12920 ep12920 em12920
    (by norm_num [dsL]) (by norm_num [tp12920]) (by norm_num [tm12920])
    (by norm_num [ep12920]) (by norm_num [em12920])
    positive12920 negative12920 tails12920.1 tails12920.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12920.1 tailGuards12920.2

theorem preserves12920 : master12920.toScalarCertificate = scalar12920 := rfl

noncomputable def tp12921 : ℝ := (1168065441 / 5000000000)
noncomputable def tm12921 : ℝ := (-((763291 / 1250000)))
noncomputable def ep12921 : ℝ := (52006069026128989 / 100000000000000000000)
noncomputable def em12921 : ℝ := (50614036752662051 / 100000000000000000000)
noncomputable def bp12921 : ℝ := (43172648736130038709 / 100000000000000000000)
noncomputable def bm12921 : ℝ := (883085918169554971 / 2000000000000000000)

theorem positive12921 :
    Eplus aL (agent12921.root+dsL) scalar12921.worldRadius world12921.frame
      agent12921.frame tp12921 ≤ -ep12921 := by
  apply positive_check (eT := (115656258448540750163 / 100000000000000000000)) (y := (38011936229907560131 / 100000000000000000000)) (u := (146245914150198303821 / 100000000000000000000))
  · norm_num [world12921, agent12921, scalar12921, tp12921, tm12921, ep12921, em12921, dsL]
  · norm_num [world12921, agent12921, scalar12921, tp12921, tm12921, ep12921, em12921, dsL]
  · norm_num [world12921, agent12921, scalar12921, tp12921, tm12921, ep12921, em12921, dsL]
  · norm_num [world12921, agent12921, scalar12921, tp12921, tm12921, ep12921, em12921, dsL]
  · norm_num [world12921, agent12921, scalar12921, tp12921, tm12921, ep12921, em12921, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12921, agent12921, tp12921, tm12921, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12921, agent12921, scalar12921, tp12921, tm12921, ep12921, em12921, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12921, agent12921, tp12921, tm12921, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12921, agent12921, scalar12921, tp12921, tm12921, ep12921, em12921, dsL]

theorem negative12921 :
    Eminus aL (agent12921.root+dsL) scalar12921.worldRadius world12921.frame
      agent12921.frame tm12921 ≤ -em12921 := by
  apply negative_check (lo := (68372974535625160447 / 100000000000000000000)) (hi := (267081931779785783 / 390625000000000000))
    (y := (-((14330412863676200803 / 20000000000000000000)))) (u := (24422439522622877349 / 50000000000000000000))
  · norm_num [world12921, agent12921, scalar12921, tp12921, tm12921, ep12921, em12921, dsL]
  · norm_num [world12921, agent12921, scalar12921, tp12921, tm12921, ep12921, em12921, dsL]
  · norm_num [world12921, agent12921, scalar12921, tp12921, tm12921, ep12921, em12921, dsL]
  · norm_num [world12921, agent12921, scalar12921, tp12921, tm12921, ep12921, em12921, dsL]
  · norm_num [world12921, agent12921, scalar12921, tp12921, tm12921, ep12921, em12921, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12921, agent12921, tp12921, tm12921, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12921, agent12921, tp12921, tm12921, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12921, agent12921, scalar12921, tp12921, tm12921, ep12921, em12921, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12921, agent12921, tp12921, tm12921, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12921, agent12921, scalar12921, tp12921, tm12921, ep12921, em12921, dsL]

theorem tails12921 :
    exp (-((12921:ℝ)*ep12921)) ≤ scalar12921.upperTail ∧
    exp (-((12921:ℝ)*em12921)) ≤ scalar12921.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12921:ℝ)) (by norm_num [ep12921]) ?_)
      (show bp12921^8 ≤ scalar12921.upperTail by norm_num [bp12921, scalar12921])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12921, bp12921, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12921:ℝ)) (by norm_num [em12921]) ?_)
      (show bm12921^8 ≤ scalar12921.lowerTail by norm_num [bm12921, scalar12921])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12921, bm12921, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12921 :
    agent12921.root+dsL+scalar12921.worldRadius < √(1/100/aL) ∧
    2*(agent12921.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12921, agent12921, scalar12921, tp12921, tm12921, ep12921, em12921, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12921, agent12921, scalar12921, tp12921, tm12921, ep12921, em12921, dsL]

noncomputable def master12921 : MasterCertificate 12921 world12921 agent12921 :=
  master scalar12921 dsL tp12921 tm12921 ep12921 em12921
    (by norm_num [dsL]) (by norm_num [tp12921]) (by norm_num [tm12921])
    (by norm_num [ep12921]) (by norm_num [em12921])
    positive12921 negative12921 tails12921.1 tails12921.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12921.1 tailGuards12921.2

theorem preserves12921 : master12921.toScalarCertificate = scalar12921 := rfl

noncomputable def tp12922 : ℝ := (584052183 / 2500000000)
noncomputable def tm12922 : ℝ := (-((381655869 / 625000000)))
noncomputable def ep12922 : ℝ := (52008431384942677 / 100000000000000000000)
noncomputable def em12922 : ℝ := (3163503087364269 / 6250000000000000000)
noncomputable def bp12922 : ℝ := (43168195034218271111 / 100000000000000000000)
noncomputable def bm12922 : ℝ := (5518758394244232047 / 12500000000000000000)

theorem positive12922 :
    Eplus aL (agent12922.root+dsL) scalar12922.worldRadius world12922.frame
      agent12922.frame tp12922 ≤ -ep12922 := by
  apply positive_check (eT := (115656457930662894387 / 100000000000000000000)) (y := (3801265004895515333 / 10000000000000000000)) (u := (36561739521278933361 / 25000000000000000000))
  · norm_num [world12922, agent12922, scalar12922, tp12922, tm12922, ep12922, em12922, dsL]
  · norm_num [world12922, agent12922, scalar12922, tp12922, tm12922, ep12922, em12922, dsL]
  · norm_num [world12922, agent12922, scalar12922, tp12922, tm12922, ep12922, em12922, dsL]
  · norm_num [world12922, agent12922, scalar12922, tp12922, tm12922, ep12922, em12922, dsL]
  · norm_num [world12922, agent12922, scalar12922, tp12922, tm12922, ep12922, em12922, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12922, agent12922, tp12922, tm12922, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12922, agent12922, scalar12922, tp12922, tm12922, ep12922, em12922, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12922, agent12922, tp12922, tm12922, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12922, agent12922, scalar12922, tp12922, tm12922, ep12922, em12922, dsL]

theorem negative12922 :
    Eminus aL (agent12922.root+dsL) scalar12922.worldRadius world12922.frame
      agent12922.frame tm12922 ≤ -em12922 := by
  apply negative_check (lo := (8546603285674082141 / 12500000000000000000)) (hi := (68372826285392657129 / 100000000000000000000))
    (y := (-((17913012598212754503 / 25000000000000000000)))) (u := (12211221461788626593 / 25000000000000000000))
  · norm_num [world12922, agent12922, scalar12922, tp12922, tm12922, ep12922, em12922, dsL]
  · norm_num [world12922, agent12922, scalar12922, tp12922, tm12922, ep12922, em12922, dsL]
  · norm_num [world12922, agent12922, scalar12922, tp12922, tm12922, ep12922, em12922, dsL]
  · norm_num [world12922, agent12922, scalar12922, tp12922, tm12922, ep12922, em12922, dsL]
  · norm_num [world12922, agent12922, scalar12922, tp12922, tm12922, ep12922, em12922, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12922, agent12922, tp12922, tm12922, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12922, agent12922, tp12922, tm12922, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12922, agent12922, scalar12922, tp12922, tm12922, ep12922, em12922, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12922, agent12922, tp12922, tm12922, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12922, agent12922, scalar12922, tp12922, tm12922, ep12922, em12922, dsL]

theorem tails12922 :
    exp (-((12922:ℝ)*ep12922)) ≤ scalar12922.upperTail ∧
    exp (-((12922:ℝ)*em12922)) ≤ scalar12922.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12922:ℝ)) (by norm_num [ep12922]) ?_)
      (show bp12922^8 ≤ scalar12922.upperTail by norm_num [bp12922, scalar12922])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12922, bp12922, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12922:ℝ)) (by norm_num [em12922]) ?_)
      (show bm12922^8 ≤ scalar12922.lowerTail by norm_num [bm12922, scalar12922])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12922, bm12922, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12922 :
    agent12922.root+dsL+scalar12922.worldRadius < √(1/100/aL) ∧
    2*(agent12922.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12922, agent12922, scalar12922, tp12922, tm12922, ep12922, em12922, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12922, agent12922, scalar12922, tp12922, tm12922, ep12922, em12922, dsL]

noncomputable def master12922 : MasterCertificate 12922 world12922 agent12922 :=
  master scalar12922 dsL tp12922 tm12922 ep12922 em12922
    (by norm_num [dsL]) (by norm_num [tp12922]) (by norm_num [tm12922])
    (by norm_num [ep12922]) (by norm_num [em12922])
    positive12922 negative12922 tails12922.1 tails12922.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12922.1 tailGuards12922.2

theorem preserves12922 : master12922.toScalarCertificate = scalar12922 := rfl

noncomputable def tp12923 : ℝ := (73008953 / 312500000)
noncomputable def tm12923 : ℝ := (-((6106659527 / 10000000000)))
noncomputable def ep12923 : ℝ := (13002698083024259 / 25000000000000000000)
noncomputable def em12923 : ℝ := (12654515191310593 / 25000000000000000000)
noncomputable def bp12923 : ℝ := (43163742521119319401 / 100000000000000000000)
noncomputable def bm12923 : ℝ := (22072919746747040759 / 50000000000000000000)

theorem positive12923 :
    Eplus aL (agent12923.root+dsL) scalar12923.worldRadius world12923.frame
      agent12923.frame tp12923 ≤ -ep12923 := by
  apply positive_check (eT := (57828328413272086119 / 50000000000000000000)) (y := (38013362647351077087 / 100000000000000000000)) (u := (146248000242306328569 / 100000000000000000000))
  · norm_num [world12923, agent12923, scalar12923, tp12923, tm12923, ep12923, em12923, dsL]
  · norm_num [world12923, agent12923, scalar12923, tp12923, tm12923, ep12923, em12923, dsL]
  · norm_num [world12923, agent12923, scalar12923, tp12923, tm12923, ep12923, em12923, dsL]
  · norm_num [world12923, agent12923, scalar12923, tp12923, tm12923, ep12923, em12923, dsL]
  · norm_num [world12923, agent12923, scalar12923, tp12923, tm12923, ep12923, em12923, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12923, agent12923, tp12923, tm12923, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12923, agent12923, scalar12923, tp12923, tm12923, ep12923, em12923, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12923, agent12923, tp12923, tm12923, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12923, agent12923, scalar12923, tp12923, tm12923, ep12923, em12923, dsL]

theorem negative12923 :
    Eminus aL (agent12923.root+dsL) scalar12923.worldRadius world12923.frame
      agent12923.frame tm12923 ≤ -em12923 := by
  apply negative_check (lo := (68372679174293281333 / 100000000000000000000)) (hi := (34186339587146640667 / 50000000000000000000))
    (y := (-((35826017125339665909 / 50000000000000000000)))) (u := (1221122343294511903 / 2500000000000000000))
  · norm_num [world12923, agent12923, scalar12923, tp12923, tm12923, ep12923, em12923, dsL]
  · norm_num [world12923, agent12923, scalar12923, tp12923, tm12923, ep12923, em12923, dsL]
  · norm_num [world12923, agent12923, scalar12923, tp12923, tm12923, ep12923, em12923, dsL]
  · norm_num [world12923, agent12923, scalar12923, tp12923, tm12923, ep12923, em12923, dsL]
  · norm_num [world12923, agent12923, scalar12923, tp12923, tm12923, ep12923, em12923, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12923, agent12923, tp12923, tm12923, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12923, agent12923, tp12923, tm12923, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12923, agent12923, scalar12923, tp12923, tm12923, ep12923, em12923, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12923, agent12923, tp12923, tm12923, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12923, agent12923, scalar12923, tp12923, tm12923, ep12923, em12923, dsL]

theorem tails12923 :
    exp (-((12923:ℝ)*ep12923)) ≤ scalar12923.upperTail ∧
    exp (-((12923:ℝ)*em12923)) ≤ scalar12923.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12923:ℝ)) (by norm_num [ep12923]) ?_)
      (show bp12923^8 ≤ scalar12923.upperTail by norm_num [bp12923, scalar12923])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12923, bp12923, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12923:ℝ)) (by norm_num [em12923]) ?_)
      (show bm12923^8 ≤ scalar12923.lowerTail by norm_num [bm12923, scalar12923])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12923, bm12923, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12923 :
    agent12923.root+dsL+scalar12923.worldRadius < √(1/100/aL) ∧
    2*(agent12923.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12923, agent12923, scalar12923, tp12923, tm12923, ep12923, em12923, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12923, agent12923, scalar12923, tp12923, tm12923, ep12923, em12923, dsL]

noncomputable def master12923 : MasterCertificate 12923 world12923 agent12923 :=
  master scalar12923 dsL tp12923 tm12923 ep12923 em12923
    (by norm_num [dsL]) (by norm_num [tp12923]) (by norm_num [tm12923])
    (by norm_num [ep12923]) (by norm_num [em12923])
    positive12923 negative12923 tails12923.1 tails12923.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12923.1 tailGuards12923.2

theorem preserves12923 : master12923.toScalarCertificate = scalar12923 := rfl

noncomputable def tp12924 : ℝ := (2336364343 / 10000000000)
noncomputable def tm12924 : ℝ := (-((6106825103 / 10000000000)))
noncomputable def ep12924 : ℝ := (3250821990343561 / 6250000000000000000)
noncomputable def em12924 : ℝ := (50620070773230747 / 100000000000000000000)
noncomputable def bp12924 : ℝ := (10789822803048529039 / 25000000000000000000)
noncomputable def bm12924 : ℝ := (882832259706304163 / 2000000000000000000)

theorem positive12924 :
    Eplus aL (agent12924.root+dsL) scalar12924.worldRadius world12924.frame
      agent12924.frame tp12924 ≤ -ep12924 := by
  apply positive_check (eT := (23131371270624693039 / 20000000000000000000)) (y := (19007038591396332339 / 50000000000000000000)) (u := (73124522619917053679 / 50000000000000000000))
  · norm_num [world12924, agent12924, scalar12924, tp12924, tm12924, ep12924, em12924, dsL]
  · norm_num [world12924, agent12924, scalar12924, tp12924, tm12924, ep12924, em12924, dsL]
  · norm_num [world12924, agent12924, scalar12924, tp12924, tm12924, ep12924, em12924, dsL]
  · norm_num [world12924, agent12924, scalar12924, tp12924, tm12924, ep12924, em12924, dsL]
  · norm_num [world12924, agent12924, scalar12924, tp12924, tm12924, ep12924, em12924, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12924, agent12924, tp12924, tm12924, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12924, agent12924, scalar12924, tp12924, tm12924, ep12924, em12924, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12924, agent12924, tp12924, tm12924, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12924, agent12924, scalar12924, tp12924, tm12924, ep12924, em12924, dsL]

theorem negative12924 :
    Eminus aL (agent12924.root+dsL) scalar12924.worldRadius world12924.frame
      agent12924.frame tm12924 ≤ -em12924 := by
  apply negative_check (lo := (17093133051539562023 / 25000000000000000000)) (hi := (68372532206158248093 / 100000000000000000000))
    (y := (-((1119562786148569591 / 1562500000000000000)))) (u := (24422450758137637821 / 50000000000000000000))
  · norm_num [world12924, agent12924, scalar12924, tp12924, tm12924, ep12924, em12924, dsL]
  · norm_num [world12924, agent12924, scalar12924, tp12924, tm12924, ep12924, em12924, dsL]
  · norm_num [world12924, agent12924, scalar12924, tp12924, tm12924, ep12924, em12924, dsL]
  · norm_num [world12924, agent12924, scalar12924, tp12924, tm12924, ep12924, em12924, dsL]
  · norm_num [world12924, agent12924, scalar12924, tp12924, tm12924, ep12924, em12924, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12924, agent12924, tp12924, tm12924, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12924, agent12924, tp12924, tm12924, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12924, agent12924, scalar12924, tp12924, tm12924, ep12924, em12924, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12924, agent12924, tp12924, tm12924, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12924, agent12924, scalar12924, tp12924, tm12924, ep12924, em12924, dsL]

theorem tails12924 :
    exp (-((12924:ℝ)*ep12924)) ≤ scalar12924.upperTail ∧
    exp (-((12924:ℝ)*em12924)) ≤ scalar12924.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12924:ℝ)) (by norm_num [ep12924]) ?_)
      (show bp12924^8 ≤ scalar12924.upperTail by norm_num [bp12924, scalar12924])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12924, bp12924, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12924:ℝ)) (by norm_num [em12924]) ?_)
      (show bm12924^8 ≤ scalar12924.lowerTail by norm_num [bm12924, scalar12924])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12924, bm12924, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12924 :
    agent12924.root+dsL+scalar12924.worldRadius < √(1/100/aL) ∧
    2*(agent12924.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12924, agent12924, scalar12924, tp12924, tm12924, ep12924, em12924, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12924, agent12924, scalar12924, tp12924, tm12924, ep12924, em12924, dsL]

noncomputable def master12924 : MasterCertificate 12924 world12924 agent12924 :=
  master scalar12924 dsL tp12924 tm12924 ep12924 em12924
    (by norm_num [dsL]) (by norm_num [tp12924]) (by norm_num [tm12924])
    (by norm_num [ep12924]) (by norm_num [em12924])
    positive12924 negative12924 tails12924.1 tails12924.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12924.1 tailGuards12924.2

theorem preserves12924 : master12924.toScalarCertificate = scalar12924 := rfl

end BstLean.Part268
