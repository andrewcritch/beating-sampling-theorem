import BstLean.Part261Checker
import BstLean.Part268Scalar9
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12575 : ℝ := (288073943 / 1250000000)
noncomputable def tm12575 : ℝ := (-((754560637 / 1250000000)))
noncomputable def ep12575 : ℝ := (25534504628565381 / 50000000000000000000)
noncomputable def em12575 : ℝ := (49799740413203131 / 100000000000000000000)
noncomputable def bp12575 : ℝ := (22404952231011719223 / 50000000000000000000)
noncomputable def bm12575 : ℝ := (45712899204094023351 / 100000000000000000000)

theorem positive12575 :
    Eplus aL (agent12575.root+dsL) scalar12575.worldRadius world12575.frame
      agent12575.frame tp12575 ≤ -ep12575 := by
  apply positive_check (eT := (115555902763728184743 / 100000000000000000000)) (y := (18884203646660127673 / 50000000000000000000)) (u := (18236274543045438913 / 12500000000000000000))
  · norm_num [world12575, agent12575, scalar12575, tp12575, tm12575, ep12575, em12575, dsL]
  · norm_num [world12575, agent12575, scalar12575, tp12575, tm12575, ep12575, em12575, dsL]
  · norm_num [world12575, agent12575, scalar12575, tp12575, tm12575, ep12575, em12575, dsL]
  · norm_num [world12575, agent12575, scalar12575, tp12575, tm12575, ep12575, em12575, dsL]
  · norm_num [world12575, agent12575, scalar12575, tp12575, tm12575, ep12575, em12575, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12575, agent12575, tp12575, tm12575, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12575, agent12575, scalar12575, tp12575, tm12575, ep12575, em12575, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12575, agent12575, tp12575, tm12575, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12575, agent12575, scalar12575, tp12575, tm12575, ep12575, em12575, dsL]

theorem negative12575 :
    Eminus aL (agent12575.root+dsL) scalar12575.worldRadius world12575.frame
      agent12575.frame tm12575 ≤ -em12575 := by
  apply negative_check (lo := (1369483145315810619 / 2000000000000000000)) (hi := (68474157265790530951 / 100000000000000000000))
    (y := (-((35849938732271703809 / 50000000000000000000)))) (u := (3051345647134482089 / 6250000000000000000))
  · norm_num [world12575, agent12575, scalar12575, tp12575, tm12575, ep12575, em12575, dsL]
  · norm_num [world12575, agent12575, scalar12575, tp12575, tm12575, ep12575, em12575, dsL]
  · norm_num [world12575, agent12575, scalar12575, tp12575, tm12575, ep12575, em12575, dsL]
  · norm_num [world12575, agent12575, scalar12575, tp12575, tm12575, ep12575, em12575, dsL]
  · norm_num [world12575, agent12575, scalar12575, tp12575, tm12575, ep12575, em12575, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12575, agent12575, tp12575, tm12575, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12575, agent12575, tp12575, tm12575, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12575, agent12575, scalar12575, tp12575, tm12575, ep12575, em12575, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12575, agent12575, tp12575, tm12575, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12575, agent12575, scalar12575, tp12575, tm12575, ep12575, em12575, dsL]

theorem tails12575 :
    exp (-((12575:ℝ)*ep12575)) ≤ scalar12575.upperTail ∧
    exp (-((12575:ℝ)*em12575)) ≤ scalar12575.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12575:ℝ)) (by norm_num [ep12575]) ?_)
      (show bp12575^8 ≤ scalar12575.upperTail by norm_num [bp12575, scalar12575])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12575, bp12575, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12575:ℝ)) (by norm_num [em12575]) ?_)
      (show bm12575^8 ≤ scalar12575.lowerTail by norm_num [bm12575, scalar12575])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12575, bm12575, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12575 :
    agent12575.root+dsL+scalar12575.worldRadius < √(1/100/aL) ∧
    2*(agent12575.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12575, agent12575, scalar12575, tp12575, tm12575, ep12575, em12575, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12575, agent12575, scalar12575, tp12575, tm12575, ep12575, em12575, dsL]

noncomputable def master12575 : MasterCertificate 12575 world12575 agent12575 :=
  master scalar12575 dsL tp12575 tm12575 ep12575 em12575
    (by norm_num [dsL]) (by norm_num [tp12575]) (by norm_num [tm12575])
    (by norm_num [ep12575]) (by norm_num [em12575])
    positive12575 negative12575 tails12575.1 tails12575.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12575.1 tailGuards12575.2

theorem preserves12575 : master12575.toScalarCertificate = scalar12575 := rfl

noncomputable def tp12576 : ℝ := (576170177 / 2500000000)
noncomputable def tm12576 : ℝ := (-((1207335463 / 2000000000)))
noncomputable def ep12576 : ℝ := (51071762001129703 / 100000000000000000000)
noncomputable def em12576 : ℝ := (24901055438160991 / 50000000000000000000)
noncomputable def bp12576 : ℝ := (22402552578598137781 / 50000000000000000000)
noncomputable def bm12576 : ℝ := (571354379830390091 / 1250000000000000000)

theorem positive12576 :
    Eplus aL (agent12576.root+dsL) scalar12576.worldRadius world12576.frame
      agent12576.frame tp12576 ≤ -ep12576 := by
  apply positive_check (eT := (23111234603490547759 / 20000000000000000000)) (y := (18884620307194139687 / 50000000000000000000)) (u := (145891412083171327279 / 100000000000000000000))
  · norm_num [world12576, agent12576, scalar12576, tp12576, tm12576, ep12576, em12576, dsL]
  · norm_num [world12576, agent12576, scalar12576, tp12576, tm12576, ep12576, em12576, dsL]
  · norm_num [world12576, agent12576, scalar12576, tp12576, tm12576, ep12576, em12576, dsL]
  · norm_num [world12576, agent12576, scalar12576, tp12576, tm12576, ep12576, em12576, dsL]
  · norm_num [world12576, agent12576, scalar12576, tp12576, tm12576, ep12576, em12576, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12576, agent12576, tp12576, tm12576, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12576, agent12576, scalar12576, tp12576, tm12576, ep12576, em12576, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12576, agent12576, tp12576, tm12576, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12576, agent12576, scalar12576, tp12576, tm12576, ep12576, em12576, dsL]

theorem negative12576 :
    Eminus aL (agent12576.root+dsL) scalar12576.worldRadius world12576.frame
      agent12576.frame tm12576 ≤ -em12576 := by
  apply negative_check (lo := (2738956614012709129 / 4000000000000000000)) (hi := (34236957675158864113 / 50000000000000000000))
    (y := (-((17924999563101862229 / 25000000000000000000)))) (u := (48821471383703620949 / 100000000000000000000))
  · norm_num [world12576, agent12576, scalar12576, tp12576, tm12576, ep12576, em12576, dsL]
  · norm_num [world12576, agent12576, scalar12576, tp12576, tm12576, ep12576, em12576, dsL]
  · norm_num [world12576, agent12576, scalar12576, tp12576, tm12576, ep12576, em12576, dsL]
  · norm_num [world12576, agent12576, scalar12576, tp12576, tm12576, ep12576, em12576, dsL]
  · norm_num [world12576, agent12576, scalar12576, tp12576, tm12576, ep12576, em12576, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12576, agent12576, tp12576, tm12576, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12576, agent12576, tp12576, tm12576, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12576, agent12576, scalar12576, tp12576, tm12576, ep12576, em12576, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12576, agent12576, tp12576, tm12576, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12576, agent12576, scalar12576, tp12576, tm12576, ep12576, em12576, dsL]

theorem tails12576 :
    exp (-((12576:ℝ)*ep12576)) ≤ scalar12576.upperTail ∧
    exp (-((12576:ℝ)*em12576)) ≤ scalar12576.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12576:ℝ)) (by norm_num [ep12576]) ?_)
      (show bp12576^8 ≤ scalar12576.upperTail by norm_num [bp12576, scalar12576])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12576, bp12576, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12576:ℝ)) (by norm_num [em12576]) ?_)
      (show bm12576^8 ≤ scalar12576.lowerTail by norm_num [bm12576, scalar12576])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12576, bm12576, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12576 :
    agent12576.root+dsL+scalar12576.worldRadius < √(1/100/aL) ∧
    2*(agent12576.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12576, agent12576, scalar12576, tp12576, tm12576, ep12576, em12576, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12576, agent12576, scalar12576, tp12576, tm12576, ep12576, em12576, dsL]

noncomputable def master12576 : MasterCertificate 12576 world12576 agent12576 :=
  master scalar12576 dsL tp12576 tm12576 ep12576 em12576
    (by norm_num [dsL]) (by norm_num [tp12576]) (by norm_num [tm12576])
    (by norm_num [ep12576]) (by norm_num [em12576])
    positive12576 negative12576 tails12576.1 tails12576.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12576.1 tailGuards12576.2

theorem preserves12576 : master12576.toScalarCertificate = scalar12576 := rfl

noncomputable def tp12577 : ℝ := (2304769813 / 10000000000)
noncomputable def tm12577 : ℝ := (-((6036869351 / 10000000000)))
noncomputable def ep12577 : ℝ := (51074512856822573 / 100000000000000000000)
noncomputable def em12577 : ℝ := (24902239789855321 / 50000000000000000000)
noncomputable def bp12577 : ℝ := (44800307388048526847 / 100000000000000000000)
noncomputable def bm12577 : ℝ := (11425950753742240833 / 25000000000000000000)

theorem positive12577 :
    Eplus aL (agent12577.root+dsL) scalar12577.worldRadius world12577.frame
      agent12577.frame tp12577 ≤ -ep12577 := by
  apply positive_check (eT := (115556442876032418087 / 100000000000000000000)) (y := (3777007343943498339 / 10000000000000000000)) (u := (72946313554225828253 / 50000000000000000000))
  · norm_num [world12577, agent12577, scalar12577, tp12577, tm12577, ep12577, em12577, dsL]
  · norm_num [world12577, agent12577, scalar12577, tp12577, tm12577, ep12577, em12577, dsL]
  · norm_num [world12577, agent12577, scalar12577, tp12577, tm12577, ep12577, em12577, dsL]
  · norm_num [world12577, agent12577, scalar12577, tp12577, tm12577, ep12577, em12577, dsL]
  · norm_num [world12577, agent12577, scalar12577, tp12577, tm12577, ep12577, em12577, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12577, agent12577, tp12577, tm12577, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12577, agent12577, scalar12577, tp12577, tm12577, ep12577, em12577, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12577, agent12577, tp12577, tm12577, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12577, agent12577, scalar12577, tp12577, tm12577, ep12577, em12577, dsL]

theorem negative12577 :
    Eminus aL (agent12577.root+dsL) scalar12577.worldRadius world12577.frame
      agent12577.frame tm12577 ≤ -em12577 := by
  apply negative_check (lo := (68473674164244454469 / 100000000000000000000)) (hi := (6847367416424445447 / 10000000000000000000))
    (y := (-((14340023604242692259 / 20000000000000000000)))) (u := (48821412910845283141 / 100000000000000000000))
  · norm_num [world12577, agent12577, scalar12577, tp12577, tm12577, ep12577, em12577, dsL]
  · norm_num [world12577, agent12577, scalar12577, tp12577, tm12577, ep12577, em12577, dsL]
  · norm_num [world12577, agent12577, scalar12577, tp12577, tm12577, ep12577, em12577, dsL]
  · norm_num [world12577, agent12577, scalar12577, tp12577, tm12577, ep12577, em12577, dsL]
  · norm_num [world12577, agent12577, scalar12577, tp12577, tm12577, ep12577, em12577, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12577, agent12577, tp12577, tm12577, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12577, agent12577, tp12577, tm12577, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12577, agent12577, scalar12577, tp12577, tm12577, ep12577, em12577, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12577, agent12577, tp12577, tm12577, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12577, agent12577, scalar12577, tp12577, tm12577, ep12577, em12577, dsL]

theorem tails12577 :
    exp (-((12577:ℝ)*ep12577)) ≤ scalar12577.upperTail ∧
    exp (-((12577:ℝ)*em12577)) ≤ scalar12577.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12577:ℝ)) (by norm_num [ep12577]) ?_)
      (show bp12577^8 ≤ scalar12577.upperTail by norm_num [bp12577, scalar12577])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12577, bp12577, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12577:ℝ)) (by norm_num [em12577]) ?_)
      (show bm12577^8 ≤ scalar12577.lowerTail by norm_num [bm12577, scalar12577])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12577, bm12577, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12577 :
    agent12577.root+dsL+scalar12577.worldRadius < √(1/100/aL) ∧
    2*(agent12577.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12577, agent12577, scalar12577, tp12577, tm12577, ep12577, em12577, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12577, agent12577, scalar12577, tp12577, tm12577, ep12577, em12577, dsL]

noncomputable def master12577 : MasterCertificate 12577 world12577 agent12577 :=
  master scalar12577 dsL tp12577 tm12577 ep12577 em12577
    (by norm_num [dsL]) (by norm_num [tp12577]) (by norm_num [tm12577])
    (by norm_num [ep12577]) (by norm_num [em12577])
    positive12577 negative12577 tails12577.1 tails12577.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12577.1 tailGuards12577.2

theorem preserves12577 : master12577.toScalarCertificate = scalar12577 := rfl

noncomputable def tp12578 : ℝ := (576214713 / 2500000000)
noncomputable def tm12578 : ℝ := (-((1509265283 / 2500000000)))
noncomputable def ep12578 : ℝ := (25538631451956987 / 50000000000000000000)
noncomputable def em12578 : ℝ := (49806847539195037 / 100000000000000000000)
noncomputable def bp12578 : ℝ := (358364083152647833 / 800000000000000000)
noncomputable def bm12578 : ℝ := (45699256359789686337 / 100000000000000000000)

theorem positive12578 :
    Eplus aL (agent12578.root+dsL) scalar12578.worldRadius world12578.frame
      agent12578.frame tp12578 ≤ -ep12578 := by
  apply positive_check (eT := (7222294518050560253 / 6250000000000000000)) (y := (18885452697896451401 / 50000000000000000000)) (u := (145893840876487624101 / 100000000000000000000))
  · norm_num [world12578, agent12578, scalar12578, tp12578, tm12578, ep12578, em12578, dsL]
  · norm_num [world12578, agent12578, scalar12578, tp12578, tm12578, ep12578, em12578, dsL]
  · norm_num [world12578, agent12578, scalar12578, tp12578, tm12578, ep12578, em12578, dsL]
  · norm_num [world12578, agent12578, scalar12578, tp12578, tm12578, ep12578, em12578, dsL]
  · norm_num [world12578, agent12578, scalar12578, tp12578, tm12578, ep12578, em12578, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12578, agent12578, tp12578, tm12578, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12578, agent12578, scalar12578, tp12578, tm12578, ep12578, em12578, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12578, agent12578, tp12578, tm12578, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12578, agent12578, scalar12578, tp12578, tm12578, ep12578, em12578, dsL]

theorem negative12578 :
    Eminus aL (agent12578.root+dsL) scalar12578.worldRadius world12578.frame
      agent12578.frame tm12578 ≤ -em12578 := by
  apply negative_check (lo := (6847343401669849707 / 10000000000000000000)) (hi := (68473434016698497071 / 100000000000000000000))
    (y := (-((17925059008962681713 / 25000000000000000000)))) (u := (390570842355727411 / 800000000000000000))
  · norm_num [world12578, agent12578, scalar12578, tp12578, tm12578, ep12578, em12578, dsL]
  · norm_num [world12578, agent12578, scalar12578, tp12578, tm12578, ep12578, em12578, dsL]
  · norm_num [world12578, agent12578, scalar12578, tp12578, tm12578, ep12578, em12578, dsL]
  · norm_num [world12578, agent12578, scalar12578, tp12578, tm12578, ep12578, em12578, dsL]
  · norm_num [world12578, agent12578, scalar12578, tp12578, tm12578, ep12578, em12578, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12578, agent12578, tp12578, tm12578, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12578, agent12578, tp12578, tm12578, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12578, agent12578, scalar12578, tp12578, tm12578, ep12578, em12578, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12578, agent12578, tp12578, tm12578, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12578, agent12578, scalar12578, tp12578, tm12578, ep12578, em12578, dsL]

theorem tails12578 :
    exp (-((12578:ℝ)*ep12578)) ≤ scalar12578.upperTail ∧
    exp (-((12578:ℝ)*em12578)) ≤ scalar12578.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12578:ℝ)) (by norm_num [ep12578]) ?_)
      (show bp12578^8 ≤ scalar12578.upperTail by norm_num [bp12578, scalar12578])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12578, bp12578, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12578:ℝ)) (by norm_num [em12578]) ?_)
      (show bm12578^8 ≤ scalar12578.lowerTail by norm_num [bm12578, scalar12578])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12578, bm12578, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12578 :
    agent12578.root+dsL+scalar12578.worldRadius < √(1/100/aL) ∧
    2*(agent12578.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12578, agent12578, scalar12578, tp12578, tm12578, ep12578, em12578, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12578, agent12578, scalar12578, tp12578, tm12578, ep12578, em12578, dsL]

noncomputable def master12578 : MasterCertificate 12578 world12578 agent12578 :=
  master scalar12578 dsL tp12578 tm12578 ep12578 em12578
    (by norm_num [dsL]) (by norm_num [tp12578]) (by norm_num [tm12578])
    (by norm_num [ep12578]) (by norm_num [em12578])
    positive12578 negative12578 tails12578.1 tails12578.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12578.1 tailGuards12578.2

theorem preserves12578 : master12578.toScalarCertificate = scalar12578 := rfl

noncomputable def tp12579 : ℝ := (2304947933 / 10000000000)
noncomputable def tm12579 : ℝ := (-((6037253083 / 10000000000)))
noncomputable def ep12579 : ℝ := (5108001185668991 / 10000000000000000000)
noncomputable def em12579 : ℝ := (3113075903136143 / 6250000000000000000)
noncomputable def bp12579 : ℝ := (44790714376512538241 / 100000000000000000000)
noncomputable def bm12579 : ℝ := (365557685117980561 / 800000000000000000)

theorem positive12579 :
    Eplus aL (agent12579.root+dsL) scalar12579.worldRadius world12579.frame
      agent12579.frame tp12579 ≤ -ep12579 := by
  apply positive_check (eT := (5777849101932074123 / 5000000000000000000)) (y := (18885869292768946903 / 50000000000000000000)) (u := (72947528227036203673 / 50000000000000000000))
  · norm_num [world12579, agent12579, scalar12579, tp12579, tm12579, ep12579, em12579, dsL]
  · norm_num [world12579, agent12579, scalar12579, tp12579, tm12579, ep12579, em12579, dsL]
  · norm_num [world12579, agent12579, scalar12579, tp12579, tm12579, ep12579, em12579, dsL]
  · norm_num [world12579, agent12579, scalar12579, tp12579, tm12579, ep12579, em12579, dsL]
  · norm_num [world12579, agent12579, scalar12579, tp12579, tm12579, ep12579, em12579, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12579, agent12579, tp12579, tm12579, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12579, agent12579, scalar12579, tp12579, tm12579, ep12579, em12579, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12579, agent12579, tp12579, tm12579, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12579, agent12579, scalar12579, tp12579, tm12579, ep12579, em12579, dsL]

theorem negative12579 :
    Eminus aL (agent12579.root+dsL) scalar12579.worldRadius world12579.frame
      agent12579.frame tm12579 ≤ -em12579 := by
  apply negative_check (lo := (68473193082144588707 / 100000000000000000000)) (hi := (17118298270536147177 / 25000000000000000000))
    (y := (-((17925089152700491849 / 25000000000000000000)))) (u := (48821296428176074107 / 100000000000000000000))
  · norm_num [world12579, agent12579, scalar12579, tp12579, tm12579, ep12579, em12579, dsL]
  · norm_num [world12579, agent12579, scalar12579, tp12579, tm12579, ep12579, em12579, dsL]
  · norm_num [world12579, agent12579, scalar12579, tp12579, tm12579, ep12579, em12579, dsL]
  · norm_num [world12579, agent12579, scalar12579, tp12579, tm12579, ep12579, em12579, dsL]
  · norm_num [world12579, agent12579, scalar12579, tp12579, tm12579, ep12579, em12579, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12579, agent12579, tp12579, tm12579, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12579, agent12579, tp12579, tm12579, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12579, agent12579, scalar12579, tp12579, tm12579, ep12579, em12579, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12579, agent12579, tp12579, tm12579, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12579, agent12579, scalar12579, tp12579, tm12579, ep12579, em12579, dsL]

theorem tails12579 :
    exp (-((12579:ℝ)*ep12579)) ≤ scalar12579.upperTail ∧
    exp (-((12579:ℝ)*em12579)) ≤ scalar12579.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12579:ℝ)) (by norm_num [ep12579]) ?_)
      (show bp12579^8 ≤ scalar12579.upperTail by norm_num [bp12579, scalar12579])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12579, bp12579, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12579:ℝ)) (by norm_num [em12579]) ?_)
      (show bm12579^8 ≤ scalar12579.lowerTail by norm_num [bm12579, scalar12579])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12579, bm12579, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12579 :
    agent12579.root+dsL+scalar12579.worldRadius < √(1/100/aL) ∧
    2*(agent12579.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12579, agent12579, scalar12579, tp12579, tm12579, ep12579, em12579, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12579, agent12579, scalar12579, tp12579, tm12579, ep12579, em12579, dsL]

noncomputable def master12579 : MasterCertificate 12579 world12579 agent12579 :=
  master scalar12579 dsL tp12579 tm12579 ep12579 em12579
    (by norm_num [dsL]) (by norm_num [tp12579]) (by norm_num [tm12579])
    (by norm_num [ep12579]) (by norm_num [em12579])
    positive12579 negative12579 tails12579.1 tails12579.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12579.1 tailGuards12579.2

theorem preserves12579 : master12579.toScalarCertificate = scalar12579 := rfl

noncomputable def tp12580 : ℝ := (2305112307 / 10000000000)
noncomputable def tm12580 : ℝ := (-((94338637 / 156250000)))
noncomputable def ep12580 : ℝ := (25542102957445659 / 50000000000000000000)
noncomputable def em12580 : ℝ := (49813154709113863 / 100000000000000000000)
noncomputable def bp12580 : ℝ := (44784900848326170513 / 100000000000000000000)
noncomputable def bm12580 : ℝ := (5711129337480478201 / 12500000000000000000)

theorem positive12580 :
    Eplus aL (agent12580.root+dsL) scalar12580.worldRadius world12580.frame
      agent12580.frame tp12580 ≤ -ep12580 := by
  apply positive_check (eT := (57778898808910828427 / 50000000000000000000)) (y := (4721480069297452753 / 12500000000000000000)) (u := (145895205221647460567 / 100000000000000000000))
  · norm_num [world12580, agent12580, scalar12580, tp12580, tm12580, ep12580, em12580, dsL]
  · norm_num [world12580, agent12580, scalar12580, tp12580, tm12580, ep12580, em12580, dsL]
  · norm_num [world12580, agent12580, scalar12580, tp12580, tm12580, ep12580, em12580, dsL]
  · norm_num [world12580, agent12580, scalar12580, tp12580, tm12580, ep12580, em12580, dsL]
  · norm_num [world12580, agent12580, scalar12580, tp12580, tm12580, ep12580, em12580, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12580, agent12580, tp12580, tm12580, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12580, agent12580, scalar12580, tp12580, tm12580, ep12580, em12580, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12580, agent12580, tp12580, tm12580, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12580, agent12580, scalar12580, tp12580, tm12580, ep12580, em12580, dsL]

theorem negative12580 :
    Eminus aL (agent12580.root+dsL) scalar12580.worldRadius world12580.frame
      agent12580.frame tm12580 ≤ -em12580 := by
  apply negative_check (lo := (68471973903715032353 / 100000000000000000000)) (hi := (34235986951857516177 / 50000000000000000000))
    (y := (-((71698553518066281387 / 100000000000000000000)))) (u := (24411088364680868899 / 50000000000000000000))
  · norm_num [world12580, agent12580, scalar12580, tp12580, tm12580, ep12580, em12580, dsL]
  · norm_num [world12580, agent12580, scalar12580, tp12580, tm12580, ep12580, em12580, dsL]
  · norm_num [world12580, agent12580, scalar12580, tp12580, tm12580, ep12580, em12580, dsL]
  · norm_num [world12580, agent12580, scalar12580, tp12580, tm12580, ep12580, em12580, dsL]
  · norm_num [world12580, agent12580, scalar12580, tp12580, tm12580, ep12580, em12580, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12580, agent12580, tp12580, tm12580, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12580, agent12580, tp12580, tm12580, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12580, agent12580, scalar12580, tp12580, tm12580, ep12580, em12580, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12580, agent12580, tp12580, tm12580, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12580, agent12580, scalar12580, tp12580, tm12580, ep12580, em12580, dsL]

theorem tails12580 :
    exp (-((12580:ℝ)*ep12580)) ≤ scalar12580.upperTail ∧
    exp (-((12580:ℝ)*em12580)) ≤ scalar12580.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12580:ℝ)) (by norm_num [ep12580]) ?_)
      (show bp12580^8 ≤ scalar12580.upperTail by norm_num [bp12580, scalar12580])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12580, bp12580, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12580:ℝ)) (by norm_num [em12580]) ?_)
      (show bm12580^8 ≤ scalar12580.lowerTail by norm_num [bm12580, scalar12580])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12580, bm12580, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12580 :
    agent12580.root+dsL+scalar12580.worldRadius < √(1/100/aL) ∧
    2*(agent12580.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12580, agent12580, scalar12580, tp12580, tm12580, ep12580, em12580, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12580, agent12580, scalar12580, tp12580, tm12580, ep12580, em12580, dsL]

noncomputable def master12580 : MasterCertificate 12580 world12580 agent12580 :=
  master scalar12580 dsL tp12580 tm12580 ep12580 em12580
    (by norm_num [dsL]) (by norm_num [tp12580]) (by norm_num [tm12580])
    (by norm_num [ep12580]) (by norm_num [em12580])
    positive12580 negative12580 tails12580.1 tails12580.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12580.1 tailGuards12580.2

theorem preserves12580 : master12580.toScalarCertificate = scalar12580 := rfl

noncomputable def tp12581 : ℝ := (2305201197 / 10000000000)
noncomputable def tm12581 : ℝ := (-((3018932181 / 5000000000)))
noncomputable def ep12581 : ℝ := (51086951961914931 / 100000000000000000000)
noncomputable def em12581 : ℝ := (49815518951228031 / 100000000000000000000)
noncomputable def bp12581 : ℝ := (44780107316581587737 / 100000000000000000000)
noncomputable def bm12581 : ℝ := (45684491283488541327 / 100000000000000000000)

theorem positive12581 :
    Eplus aL (agent12581.root+dsL) scalar12581.worldRadius world12581.frame
      agent12581.frame tp12581 ≤ -ep12581 := by
  apply positive_check (eT := (115558066037305602587 / 100000000000000000000)) (y := (9443167781952314787 / 25000000000000000000)) (u := (145896416993489466633 / 100000000000000000000))
  · norm_num [world12581, agent12581, scalar12581, tp12581, tm12581, ep12581, em12581, dsL]
  · norm_num [world12581, agent12581, scalar12581, tp12581, tm12581, ep12581, em12581, dsL]
  · norm_num [world12581, agent12581, scalar12581, tp12581, tm12581, ep12581, em12581, dsL]
  · norm_num [world12581, agent12581, scalar12581, tp12581, tm12581, ep12581, em12581, dsL]
  · norm_num [world12581, agent12581, scalar12581, tp12581, tm12581, ep12581, em12581, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12581, agent12581, tp12581, tm12581, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12581, agent12581, scalar12581, tp12581, tm12581, ep12581, em12581, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12581, agent12581, tp12581, tm12581, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12581, agent12581, scalar12581, tp12581, tm12581, ep12581, em12581, dsL]

theorem negative12581 :
    Eminus aL (agent12581.root+dsL) scalar12581.worldRadius world12581.frame
      agent12581.frame tm12581 ≤ -em12581 := by
  apply negative_check (lo := (34235867207235796503 / 50000000000000000000)) (hi := (68471734414471593007 / 100000000000000000000))
    (y := (-((1433973439721391121 / 2000000000000000000)))) (u := (24411059445369035717 / 50000000000000000000))
  · norm_num [world12581, agent12581, scalar12581, tp12581, tm12581, ep12581, em12581, dsL]
  · norm_num [world12581, agent12581, scalar12581, tp12581, tm12581, ep12581, em12581, dsL]
  · norm_num [world12581, agent12581, scalar12581, tp12581, tm12581, ep12581, em12581, dsL]
  · norm_num [world12581, agent12581, scalar12581, tp12581, tm12581, ep12581, em12581, dsL]
  · norm_num [world12581, agent12581, scalar12581, tp12581, tm12581, ep12581, em12581, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12581, agent12581, tp12581, tm12581, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12581, agent12581, tp12581, tm12581, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12581, agent12581, scalar12581, tp12581, tm12581, ep12581, em12581, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12581, agent12581, tp12581, tm12581, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12581, agent12581, scalar12581, tp12581, tm12581, ep12581, em12581, dsL]

theorem tails12581 :
    exp (-((12581:ℝ)*ep12581)) ≤ scalar12581.upperTail ∧
    exp (-((12581:ℝ)*em12581)) ≤ scalar12581.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12581:ℝ)) (by norm_num [ep12581]) ?_)
      (show bp12581^8 ≤ scalar12581.upperTail by norm_num [bp12581, scalar12581])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12581, bp12581, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12581:ℝ)) (by norm_num [em12581]) ?_)
      (show bm12581^8 ≤ scalar12581.lowerTail by norm_num [bm12581, scalar12581])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12581, bm12581, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12581 :
    agent12581.root+dsL+scalar12581.worldRadius < √(1/100/aL) ∧
    2*(agent12581.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12581, agent12581, scalar12581, tp12581, tm12581, ep12581, em12581, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12581, agent12581, scalar12581, tp12581, tm12581, ep12581, em12581, dsL]

noncomputable def master12581 : MasterCertificate 12581 world12581 agent12581 :=
  master scalar12581 dsL tp12581 tm12581 ep12581 em12581
    (by norm_num [dsL]) (by norm_num [tp12581]) (by norm_num [tm12581])
    (by norm_num [ep12581]) (by norm_num [em12581])
    positive12581 negative12581 tails12581.1 tails12581.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12581.1 tailGuards12581.2

theorem preserves12581 : master12581.toScalarCertificate = scalar12581 := rfl

noncomputable def tp12582 : ℝ := (1152645051 / 5000000000)
noncomputable def tm12582 : ℝ := (-((6038055851 / 10000000000)))
noncomputable def ep12582 : ℝ := (25544848062695539 / 50000000000000000000)
noncomputable def em12582 : ℝ := (49817881437909639 / 100000000000000000000)
noncomputable def bp12582 : ℝ := (11193828829230984149 / 25000000000000000000)
noncomputable def bm12582 : ℝ := (45679949310102114779 / 100000000000000000000)

theorem positive12582 :
    Eplus aL (agent12582.root+dsL) scalar12582.worldRadius world12582.frame
      agent12582.frame tp12582 ≤ -ep12582 := by
  apply positive_check (eT := (57779167299090657143 / 50000000000000000000)) (y := (944337562666893473 / 2500000000000000000)) (u := (72948814975254714441 / 50000000000000000000))
  · norm_num [world12582, agent12582, scalar12582, tp12582, tm12582, ep12582, em12582, dsL]
  · norm_num [world12582, agent12582, scalar12582, tp12582, tm12582, ep12582, em12582, dsL]
  · norm_num [world12582, agent12582, scalar12582, tp12582, tm12582, ep12582, em12582, dsL]
  · norm_num [world12582, agent12582, scalar12582, tp12582, tm12582, ep12582, em12582, dsL]
  · norm_num [world12582, agent12582, scalar12582, tp12582, tm12582, ep12582, em12582, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12582, agent12582, tp12582, tm12582, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12582, agent12582, scalar12582, tp12582, tm12582, ep12582, em12582, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12582, agent12582, tp12582, tm12582, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12582, agent12582, scalar12582, tp12582, tm12582, ep12582, em12582, dsL]

theorem negative12582 :
    Eminus aL (agent12582.root+dsL) scalar12582.worldRadius world12582.frame
      agent12582.frame tm12582 ≤ -em12582 := by
  apply negative_check (lo := (855893691491959937 / 1250000000000000000)) (hi := (68471495319356794961 / 100000000000000000000))
    (y := (-((35849395097620229317 / 50000000000000000000)))) (u := (1952882447142008967 / 4000000000000000000))
  · norm_num [world12582, agent12582, scalar12582, tp12582, tm12582, ep12582, em12582, dsL]
  · norm_num [world12582, agent12582, scalar12582, tp12582, tm12582, ep12582, em12582, dsL]
  · norm_num [world12582, agent12582, scalar12582, tp12582, tm12582, ep12582, em12582, dsL]
  · norm_num [world12582, agent12582, scalar12582, tp12582, tm12582, ep12582, em12582, dsL]
  · norm_num [world12582, agent12582, scalar12582, tp12582, tm12582, ep12582, em12582, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12582, agent12582, tp12582, tm12582, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12582, agent12582, tp12582, tm12582, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12582, agent12582, scalar12582, tp12582, tm12582, ep12582, em12582, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12582, agent12582, tp12582, tm12582, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12582, agent12582, scalar12582, tp12582, tm12582, ep12582, em12582, dsL]

theorem tails12582 :
    exp (-((12582:ℝ)*ep12582)) ≤ scalar12582.upperTail ∧
    exp (-((12582:ℝ)*em12582)) ≤ scalar12582.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12582:ℝ)) (by norm_num [ep12582]) ?_)
      (show bp12582^8 ≤ scalar12582.upperTail by norm_num [bp12582, scalar12582])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12582, bp12582, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12582:ℝ)) (by norm_num [em12582]) ?_)
      (show bm12582^8 ≤ scalar12582.lowerTail by norm_num [bm12582, scalar12582])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12582, bm12582, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12582 :
    agent12582.root+dsL+scalar12582.worldRadius < √(1/100/aL) ∧
    2*(agent12582.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12582, agent12582, scalar12582, tp12582, tm12582, ep12582, em12582, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12582, agent12582, scalar12582, tp12582, tm12582, ep12582, em12582, dsL]

noncomputable def master12582 : MasterCertificate 12582 world12582 agent12582 :=
  master scalar12582 dsL tp12582 tm12582 ep12582 em12582
    (by norm_num [dsL]) (by norm_num [tp12582]) (by norm_num [tm12582])
    (by norm_num [ep12582]) (by norm_num [em12582])
    positive12582 negative12582 tails12582.1 tails12582.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12582.1 tailGuards12582.2

theorem preserves12582 : master12582.toScalarCertificate = scalar12582 := rfl

noncomputable def tp12583 : ℝ := (1152689469 / 5000000000)
noncomputable def tm12583 : ℝ := (-((3019123639 / 5000000000)))
noncomputable def ep12583 : ℝ := (6386554916416213 / 12500000000000000000)
noncomputable def em12583 : ℝ := (12455060755027429 / 25000000000000000000)
noncomputable def bp12583 : ℝ := (5596315524650705361 / 12500000000000000000)
noncomputable def bm12583 : ℝ := (1827016326732276521 / 4000000000000000000)

theorem positive12583 :
    Eplus aL (agent12583.root+dsL) scalar12583.worldRadius world12583.frame
      agent12583.frame tp12583 ≤ -ep12583 := by
  apply positive_check (eT := (115558602691544748911 / 100000000000000000000)) (y := (9443583253248085339 / 25000000000000000000)) (u := (9118677602785845751 / 6250000000000000000))
  · norm_num [world12583, agent12583, scalar12583, tp12583, tm12583, ep12583, em12583, dsL]
  · norm_num [world12583, agent12583, scalar12583, tp12583, tm12583, ep12583, em12583, dsL]
  · norm_num [world12583, agent12583, scalar12583, tp12583, tm12583, ep12583, em12583, dsL]
  · norm_num [world12583, agent12583, scalar12583, tp12583, tm12583, ep12583, em12583, dsL]
  · norm_num [world12583, agent12583, scalar12583, tp12583, tm12583, ep12583, em12583, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12583, agent12583, tp12583, tm12583, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12583, agent12583, scalar12583, tp12583, tm12583, ep12583, em12583, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12583, agent12583, tp12583, tm12583, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12583, agent12583, scalar12583, tp12583, tm12583, ep12583, em12583, dsL]

theorem negative12583 :
    Eminus aL (agent12583.root+dsL) scalar12583.worldRadius world12583.frame
      agent12583.frame tm12583 ≤ -em12583 := by
  apply negative_check (lo := (68471256433685999459 / 100000000000000000000)) (hi := (3423562821684299973 / 5000000000000000000))
    (y := (-((71698908408930246083 / 100000000000000000000)))) (u := (48822003464224387849 / 100000000000000000000))
  · norm_num [world12583, agent12583, scalar12583, tp12583, tm12583, ep12583, em12583, dsL]
  · norm_num [world12583, agent12583, scalar12583, tp12583, tm12583, ep12583, em12583, dsL]
  · norm_num [world12583, agent12583, scalar12583, tp12583, tm12583, ep12583, em12583, dsL]
  · norm_num [world12583, agent12583, scalar12583, tp12583, tm12583, ep12583, em12583, dsL]
  · norm_num [world12583, agent12583, scalar12583, tp12583, tm12583, ep12583, em12583, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12583, agent12583, tp12583, tm12583, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12583, agent12583, tp12583, tm12583, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12583, agent12583, scalar12583, tp12583, tm12583, ep12583, em12583, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12583, agent12583, tp12583, tm12583, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12583, agent12583, scalar12583, tp12583, tm12583, ep12583, em12583, dsL]

theorem tails12583 :
    exp (-((12583:ℝ)*ep12583)) ≤ scalar12583.upperTail ∧
    exp (-((12583:ℝ)*em12583)) ≤ scalar12583.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12583:ℝ)) (by norm_num [ep12583]) ?_)
      (show bp12583^8 ≤ scalar12583.upperTail by norm_num [bp12583, scalar12583])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12583, bp12583, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12583:ℝ)) (by norm_num [em12583]) ?_)
      (show bm12583^8 ≤ scalar12583.lowerTail by norm_num [bm12583, scalar12583])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12583, bm12583, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12583 :
    agent12583.root+dsL+scalar12583.worldRadius < √(1/100/aL) ∧
    2*(agent12583.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12583, agent12583, scalar12583, tp12583, tm12583, ep12583, em12583, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12583, agent12583, scalar12583, tp12583, tm12583, ep12583, em12583, dsL]

noncomputable def master12583 : MasterCertificate 12583 world12583 agent12583 :=
  master scalar12583 dsL tp12583 tm12583 ep12583 em12583
    (by norm_num [dsL]) (by norm_num [tp12583]) (by norm_num [tm12583])
    (by norm_num [ep12583]) (by norm_num [em12583])
    positive12583 negative12583 tails12583.1 tails12583.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12583.1 tailGuards12583.2

theorem preserves12583 : master12583.toScalarCertificate = scalar12583 := rfl

noncomputable def tp12584 : ℝ := (1152733877 / 5000000000)
noncomputable def tm12584 : ℝ := (-((1509609641 / 2500000000)))
noncomputable def ep12584 : ℝ := (12773795203099073 / 25000000000000000000)
noncomputable def em12584 : ℝ := (996452060322207 / 2000000000000000000)
noncomputable def bp12584 : ℝ := (2238286724887241417 / 5000000000000000000)
noncomputable def bm12584 : ℝ := (45670868347847636617 / 100000000000000000000)

theorem positive12584 :
    Eplus aL (agent12584.root+dsL) scalar12584.worldRadius world12584.frame
      agent12584.frame tp12584 ≤ -ep12584 := by
  apply positive_check (eT := (115558870672578540113 / 100000000000000000000)) (y := (2360947728664194449 / 6250000000000000000)) (u := (145900053551966153369 / 100000000000000000000))
  · norm_num [world12584, agent12584, scalar12584, tp12584, tm12584, ep12584, em12584, dsL]
  · norm_num [world12584, agent12584, scalar12584, tp12584, tm12584, ep12584, em12584, dsL]
  · norm_num [world12584, agent12584, scalar12584, tp12584, tm12584, ep12584, em12584, dsL]
  · norm_num [world12584, agent12584, scalar12584, tp12584, tm12584, ep12584, em12584, dsL]
  · norm_num [world12584, agent12584, scalar12584, tp12584, tm12584, ep12584, em12584, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12584, agent12584, tp12584, tm12584, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12584, agent12584, scalar12584, tp12584, tm12584, ep12584, em12584, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12584, agent12584, tp12584, tm12584, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12584, agent12584, scalar12584, tp12584, tm12584, ep12584, em12584, dsL]

theorem negative12584 :
    Eminus aL (agent12584.root+dsL) scalar12584.worldRadius world12584.frame
      agent12584.frame tm12584 ≤ -em12584 := by
  apply negative_check (lo := (2139719315523838479 / 3125000000000000000)) (hi := (68471018096762831329 / 100000000000000000000))
    (y := (-((35849513068269083479 / 50000000000000000000)))) (u := (48821945987281403493 / 100000000000000000000))
  · norm_num [world12584, agent12584, scalar12584, tp12584, tm12584, ep12584, em12584, dsL]
  · norm_num [world12584, agent12584, scalar12584, tp12584, tm12584, ep12584, em12584, dsL]
  · norm_num [world12584, agent12584, scalar12584, tp12584, tm12584, ep12584, em12584, dsL]
  · norm_num [world12584, agent12584, scalar12584, tp12584, tm12584, ep12584, em12584, dsL]
  · norm_num [world12584, agent12584, scalar12584, tp12584, tm12584, ep12584, em12584, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12584, agent12584, tp12584, tm12584, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12584, agent12584, tp12584, tm12584, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12584, agent12584, scalar12584, tp12584, tm12584, ep12584, em12584, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12584, agent12584, tp12584, tm12584, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12584, agent12584, scalar12584, tp12584, tm12584, ep12584, em12584, dsL]

theorem tails12584 :
    exp (-((12584:ℝ)*ep12584)) ≤ scalar12584.upperTail ∧
    exp (-((12584:ℝ)*em12584)) ≤ scalar12584.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12584:ℝ)) (by norm_num [ep12584]) ?_)
      (show bp12584^8 ≤ scalar12584.upperTail by norm_num [bp12584, scalar12584])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12584, bp12584, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12584:ℝ)) (by norm_num [em12584]) ?_)
      (show bm12584^8 ≤ scalar12584.lowerTail by norm_num [bm12584, scalar12584])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12584, bm12584, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12584 :
    agent12584.root+dsL+scalar12584.worldRadius < √(1/100/aL) ∧
    2*(agent12584.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12584, agent12584, scalar12584, tp12584, tm12584, ep12584, em12584, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12584, agent12584, scalar12584, tp12584, tm12584, ep12584, em12584, dsL]

noncomputable def master12584 : MasterCertificate 12584 world12584 agent12584 :=
  master scalar12584 dsL tp12584 tm12584 ep12584 em12584
    (by norm_num [dsL]) (by norm_num [tp12584]) (by norm_num [tm12584])
    (by norm_num [ep12584]) (by norm_num [em12584])
    positive12584 negative12584 tails12584.1 tails12584.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12584.1 tailGuards12584.2

theorem preserves12584 : master12584.toScalarCertificate = scalar12584 := rfl

noncomputable def tp12585 : ℝ := (2305556501 / 10000000000)
noncomputable def tm12585 : ℝ := (-((3019314961 / 5000000000)))
noncomputable def ep12585 : ℝ := (25548960672073439 / 50000000000000000000)
noncomputable def em12585 : ℝ := (24912481060686671 / 50000000000000000000)
noncomputable def bp12585 : ℝ := (5595118209047559529 / 12500000000000000000)
noncomputable def bm12585 : ℝ := (22833164674539967017 / 50000000000000000000)

theorem positive12585 :
    Eplus aL (agent12585.root+dsL) scalar12585.worldRadius world12585.frame
      agent12585.frame tp12585 ≤ -ep12585 := by
  apply positive_check (eT := (57779569093053760123 / 50000000000000000000)) (y := (37775993533156410861 / 100000000000000000000)) (u := (145901264344372837669 / 100000000000000000000))
  · norm_num [world12585, agent12585, scalar12585, tp12585, tm12585, ep12585, em12585, dsL]
  · norm_num [world12585, agent12585, scalar12585, tp12585, tm12585, ep12585, em12585, dsL]
  · norm_num [world12585, agent12585, scalar12585, tp12585, tm12585, ep12585, em12585, dsL]
  · norm_num [world12585, agent12585, scalar12585, tp12585, tm12585, ep12585, em12585, dsL]
  · norm_num [world12585, agent12585, scalar12585, tp12585, tm12585, ep12585, em12585, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12585, agent12585, tp12585, tm12585, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12585, agent12585, scalar12585, tp12585, tm12585, ep12585, em12585, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12585, agent12585, tp12585, tm12585, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12585, agent12585, scalar12585, tp12585, tm12585, ep12585, em12585, dsL]

theorem negative12585 :
    Eminus aL (agent12585.root+dsL) scalar12585.worldRadius world12585.frame
      agent12585.frame tm12585 ≤ -em12585 := by
  apply negative_check (lo := (34235389696899190163 / 50000000000000000000)) (hi := (68470779393798380327 / 100000000000000000000))
    (y := (-((71699145589351251437 / 100000000000000000000)))) (u := (48821887668128351041 / 100000000000000000000))
  · norm_num [world12585, agent12585, scalar12585, tp12585, tm12585, ep12585, em12585, dsL]
  · norm_num [world12585, agent12585, scalar12585, tp12585, tm12585, ep12585, em12585, dsL]
  · norm_num [world12585, agent12585, scalar12585, tp12585, tm12585, ep12585, em12585, dsL]
  · norm_num [world12585, agent12585, scalar12585, tp12585, tm12585, ep12585, em12585, dsL]
  · norm_num [world12585, agent12585, scalar12585, tp12585, tm12585, ep12585, em12585, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12585, agent12585, tp12585, tm12585, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12585, agent12585, tp12585, tm12585, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12585, agent12585, scalar12585, tp12585, tm12585, ep12585, em12585, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12585, agent12585, tp12585, tm12585, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12585, agent12585, scalar12585, tp12585, tm12585, ep12585, em12585, dsL]

theorem tails12585 :
    exp (-((12585:ℝ)*ep12585)) ≤ scalar12585.upperTail ∧
    exp (-((12585:ℝ)*em12585)) ≤ scalar12585.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12585:ℝ)) (by norm_num [ep12585]) ?_)
      (show bp12585^8 ≤ scalar12585.upperTail by norm_num [bp12585, scalar12585])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12585, bp12585, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12585:ℝ)) (by norm_num [em12585]) ?_)
      (show bm12585^8 ≤ scalar12585.lowerTail by norm_num [bm12585, scalar12585])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12585, bm12585, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12585 :
    agent12585.root+dsL+scalar12585.worldRadius < √(1/100/aL) ∧
    2*(agent12585.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12585, agent12585, scalar12585, tp12585, tm12585, ep12585, em12585, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12585, agent12585, scalar12585, tp12585, tm12585, ep12585, em12585, dsL]

noncomputable def master12585 : MasterCertificate 12585 world12585 agent12585 :=
  master scalar12585 dsL tp12585 tm12585 ep12585 em12585
    (by norm_num [dsL]) (by norm_num [tp12585]) (by norm_num [tm12585])
    (by norm_num [ep12585]) (by norm_num [em12585])
    positive12585 negative12585 tails12585.1 tails12585.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12585.1 tailGuards12585.2

theorem preserves12585 : master12585.toScalarCertificate = scalar12585 := rfl

noncomputable def tp12586 : ℝ := (2305645233 / 10000000000)
noncomputable def tm12586 : ℝ := (-((3019410519 / 5000000000)))
noncomputable def ep12586 : ℝ := (12775164916089923 / 25000000000000000000)
noncomputable def em12586 : ℝ := (49827319184948093 / 100000000000000000000)
noncomputable def bp12586 : ℝ := (2797259913116532223 / 6250000000000000000)
noncomputable def bm12586 : ℝ := (9132358399762833069 / 20000000000000000000)

theorem positive12586 :
    Eplus aL (agent12586.root+dsL) scalar12586.worldRadius world12586.frame
      agent12586.frame tp12586 ≤ -ep12586 := by
  apply positive_check (eT := (115559405623567172603 / 100000000000000000000)) (y := (7555364716323873307 / 20000000000000000000)) (u := (145902475400601130881 / 100000000000000000000))
  · norm_num [world12586, agent12586, scalar12586, tp12586, tm12586, ep12586, em12586, dsL]
  · norm_num [world12586, agent12586, scalar12586, tp12586, tm12586, ep12586, em12586, dsL]
  · norm_num [world12586, agent12586, scalar12586, tp12586, tm12586, ep12586, em12586, dsL]
  · norm_num [world12586, agent12586, scalar12586, tp12586, tm12586, ep12586, em12586, dsL]
  · norm_num [world12586, agent12586, scalar12586, tp12586, tm12586, ep12586, em12586, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12586, agent12586, tp12586, tm12586, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12586, agent12586, scalar12586, tp12586, tm12586, ep12586, em12586, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12586, agent12586, tp12586, tm12586, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12586, agent12586, scalar12586, tp12586, tm12586, ep12586, em12586, dsL]

theorem negative12586 :
    Eminus aL (agent12586.root+dsL) scalar12586.worldRadius world12586.frame
      agent12586.frame tm12586 ≤ -em12586 := by
  apply negative_check (lo := (13694108334662881299 / 20000000000000000000)) (hi := (2139704427291075203 / 3125000000000000000))
    (y := (-((2867970521113914637 / 4000000000000000000)))) (u := (48821830332471121851 / 100000000000000000000))
  · norm_num [world12586, agent12586, scalar12586, tp12586, tm12586, ep12586, em12586, dsL]
  · norm_num [world12586, agent12586, scalar12586, tp12586, tm12586, ep12586, em12586, dsL]
  · norm_num [world12586, agent12586, scalar12586, tp12586, tm12586, ep12586, em12586, dsL]
  · norm_num [world12586, agent12586, scalar12586, tp12586, tm12586, ep12586, em12586, dsL]
  · norm_num [world12586, agent12586, scalar12586, tp12586, tm12586, ep12586, em12586, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12586, agent12586, tp12586, tm12586, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12586, agent12586, tp12586, tm12586, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12586, agent12586, scalar12586, tp12586, tm12586, ep12586, em12586, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12586, agent12586, tp12586, tm12586, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12586, agent12586, scalar12586, tp12586, tm12586, ep12586, em12586, dsL]

theorem tails12586 :
    exp (-((12586:ℝ)*ep12586)) ≤ scalar12586.upperTail ∧
    exp (-((12586:ℝ)*em12586)) ≤ scalar12586.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12586:ℝ)) (by norm_num [ep12586]) ?_)
      (show bp12586^8 ≤ scalar12586.upperTail by norm_num [bp12586, scalar12586])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12586, bp12586, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12586:ℝ)) (by norm_num [em12586]) ?_)
      (show bm12586^8 ≤ scalar12586.lowerTail by norm_num [bm12586, scalar12586])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12586, bm12586, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12586 :
    agent12586.root+dsL+scalar12586.worldRadius < √(1/100/aL) ∧
    2*(agent12586.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12586, agent12586, scalar12586, tp12586, tm12586, ep12586, em12586, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12586, agent12586, scalar12586, tp12586, tm12586, ep12586, em12586, dsL]

noncomputable def master12586 : MasterCertificate 12586 world12586 agent12586 :=
  master scalar12586 dsL tp12586 tm12586 ep12586 em12586
    (by norm_num [dsL]) (by norm_num [tp12586]) (by norm_num [tm12586])
    (by norm_num [ep12586]) (by norm_num [em12586])
    positive12586 negative12586 tails12586.1 tails12586.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12586.1 tailGuards12586.2

theorem preserves12586 : master12586.toScalarCertificate = scalar12586 := rfl

noncomputable def tp12587 : ℝ := (2305734211 / 10000000000)
noncomputable def tm12587 : ℝ := (-((6039012511 / 10000000000)))
noncomputable def ep12587 : ℝ := (51103411147437939 / 100000000000000000000)
noncomputable def em12587 : ℝ := (6228710882358973 / 12500000000000000000)
noncomputable def bp12587 : ℝ := (11187840621222417799 / 25000000000000000000)
noncomputable def bm12587 : ℝ := (4565724706461150097 / 10000000000000000000)

theorem positive12587 :
    Eplus aL (agent12587.root+dsL) scalar12587.worldRadius world12587.frame
      agent12587.frame tp12587 ≤ -ep12587 := by
  apply positive_check (eT := (115559674876663352729 / 100000000000000000000)) (y := (37777658946424908883 / 100000000000000000000)) (u := (18237961777952730597 / 12500000000000000000))
  · norm_num [world12587, agent12587, scalar12587, tp12587, tm12587, ep12587, em12587, dsL]
  · norm_num [world12587, agent12587, scalar12587, tp12587, tm12587, ep12587, em12587, dsL]
  · norm_num [world12587, agent12587, scalar12587, tp12587, tm12587, ep12587, em12587, dsL]
  · norm_num [world12587, agent12587, scalar12587, tp12587, tm12587, ep12587, em12587, dsL]
  · norm_num [world12587, agent12587, scalar12587, tp12587, tm12587, ep12587, em12587, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12587, agent12587, tp12587, tm12587, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12587, agent12587, scalar12587, tp12587, tm12587, ep12587, em12587, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12587, agent12587, tp12587, tm12587, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12587, agent12587, scalar12587, tp12587, tm12587, ep12587, em12587, dsL]

theorem negative12587 :
    Eminus aL (agent12587.root+dsL) scalar12587.worldRadius world12587.frame
      agent12587.frame tm12587 ≤ -em12587 := by
  apply negative_check (lo := (34235151181430563811 / 50000000000000000000)) (hi := (68470302362861127623 / 100000000000000000000))
    (y := (-((71699383882765151237 / 100000000000000000000)))) (u := (48821771328924110719 / 100000000000000000000))
  · norm_num [world12587, agent12587, scalar12587, tp12587, tm12587, ep12587, em12587, dsL]
  · norm_num [world12587, agent12587, scalar12587, tp12587, tm12587, ep12587, em12587, dsL]
  · norm_num [world12587, agent12587, scalar12587, tp12587, tm12587, ep12587, em12587, dsL]
  · norm_num [world12587, agent12587, scalar12587, tp12587, tm12587, ep12587, em12587, dsL]
  · norm_num [world12587, agent12587, scalar12587, tp12587, tm12587, ep12587, em12587, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12587, agent12587, tp12587, tm12587, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12587, agent12587, tp12587, tm12587, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12587, agent12587, scalar12587, tp12587, tm12587, ep12587, em12587, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12587, agent12587, tp12587, tm12587, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12587, agent12587, scalar12587, tp12587, tm12587, ep12587, em12587, dsL]

theorem tails12587 :
    exp (-((12587:ℝ)*ep12587)) ≤ scalar12587.upperTail ∧
    exp (-((12587:ℝ)*em12587)) ≤ scalar12587.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12587:ℝ)) (by norm_num [ep12587]) ?_)
      (show bp12587^8 ≤ scalar12587.upperTail by norm_num [bp12587, scalar12587])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12587, bp12587, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12587:ℝ)) (by norm_num [em12587]) ?_)
      (show bm12587^8 ≤ scalar12587.lowerTail by norm_num [bm12587, scalar12587])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12587, bm12587, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12587 :
    agent12587.root+dsL+scalar12587.worldRadius < √(1/100/aL) ∧
    2*(agent12587.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12587, agent12587, scalar12587, tp12587, tm12587, ep12587, em12587, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12587, agent12587, scalar12587, tp12587, tm12587, ep12587, em12587, dsL]

noncomputable def master12587 : MasterCertificate 12587 world12587 agent12587 :=
  master scalar12587 dsL tp12587 tm12587 ep12587 em12587
    (by norm_num [dsL]) (by norm_num [tp12587]) (by norm_num [tm12587])
    (by norm_num [ep12587]) (by norm_num [em12587])
    positive12587 negative12587 tails12587.1 tails12587.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12587.1 tailGuards12587.2

theorem preserves12587 : master12587.toScalarCertificate = scalar12587 := rfl

noncomputable def tp12588 : ℝ := (1152911741 / 5000000000)
noncomputable def tm12588 : ℝ := (-((3019602201 / 5000000000)))
noncomputable def ep12588 : ℝ := (12776543499075239 / 25000000000000000000)
noncomputable def em12588 : ℝ := (9966412840635309 / 20000000000000000000)
noncomputable def bp12588 : ℝ := (4474655856357177997 / 10000000000000000000)
noncomputable def bm12588 : ℝ := (22826347826602058663 / 50000000000000000000)

theorem positive12588 :
    Eplus aL (agent12588.root+dsL) scalar12588.worldRadius world12588.frame
      agent12588.frame tp12588 ≤ -ep12588 := by
  apply positive_check (eT := (57779973142984836069 / 50000000000000000000)) (y := (7555700069430202153 / 20000000000000000000)) (u := (18238115232941141263 / 12500000000000000000))
  · norm_num [world12588, agent12588, scalar12588, tp12588, tm12588, ep12588, em12588, dsL]
  · norm_num [world12588, agent12588, scalar12588, tp12588, tm12588, ep12588, em12588, dsL]
  · norm_num [world12588, agent12588, scalar12588, tp12588, tm12588, ep12588, em12588, dsL]
  · norm_num [world12588, agent12588, scalar12588, tp12588, tm12588, ep12588, em12588, dsL]
  · norm_num [world12588, agent12588, scalar12588, tp12588, tm12588, ep12588, em12588, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12588, agent12588, tp12588, tm12588, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12588, agent12588, scalar12588, tp12588, tm12588, ep12588, em12588, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12588, agent12588, tp12588, tm12588, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12588, agent12588, scalar12588, tp12588, tm12588, ep12588, em12588, dsL]

theorem negative12588 :
    Eminus aL (agent12588.root+dsL) scalar12588.worldRadius world12588.frame
      agent12588.frame tm12588 ≤ -em12588 := by
  apply negative_check (lo := (3423503060027547763 / 5000000000000000000)) (hi := (68470061200550955261 / 100000000000000000000))
    (y := (-((71699508318160461889 / 100000000000000000000)))) (u := (24410855288698879059 / 50000000000000000000))
  · norm_num [world12588, agent12588, scalar12588, tp12588, tm12588, ep12588, em12588, dsL]
  · norm_num [world12588, agent12588, scalar12588, tp12588, tm12588, ep12588, em12588, dsL]
  · norm_num [world12588, agent12588, scalar12588, tp12588, tm12588, ep12588, em12588, dsL]
  · norm_num [world12588, agent12588, scalar12588, tp12588, tm12588, ep12588, em12588, dsL]
  · norm_num [world12588, agent12588, scalar12588, tp12588, tm12588, ep12588, em12588, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12588, agent12588, tp12588, tm12588, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12588, agent12588, tp12588, tm12588, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12588, agent12588, scalar12588, tp12588, tm12588, ep12588, em12588, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12588, agent12588, tp12588, tm12588, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12588, agent12588, scalar12588, tp12588, tm12588, ep12588, em12588, dsL]

theorem tails12588 :
    exp (-((12588:ℝ)*ep12588)) ≤ scalar12588.upperTail ∧
    exp (-((12588:ℝ)*em12588)) ≤ scalar12588.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12588:ℝ)) (by norm_num [ep12588]) ?_)
      (show bp12588^8 ≤ scalar12588.upperTail by norm_num [bp12588, scalar12588])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12588, bp12588, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12588:ℝ)) (by norm_num [em12588]) ?_)
      (show bm12588^8 ≤ scalar12588.lowerTail by norm_num [bm12588, scalar12588])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12588, bm12588, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12588 :
    agent12588.root+dsL+scalar12588.worldRadius < √(1/100/aL) ∧
    2*(agent12588.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12588, agent12588, scalar12588, tp12588, tm12588, ep12588, em12588, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12588, agent12588, scalar12588, tp12588, tm12588, ep12588, em12588, dsL]

noncomputable def master12588 : MasterCertificate 12588 world12588 agent12588 :=
  master scalar12588 dsL tp12588 tm12588 ep12588 em12588
    (by norm_num [dsL]) (by norm_num [tp12588]) (by norm_num [tm12588])
    (by norm_num [ep12588]) (by norm_num [em12588])
    positive12588 negative12588 tails12588.1 tails12588.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12588.1 tailGuards12588.2

theorem preserves12588 : master12588.toScalarCertificate = scalar12588 := rfl

noncomputable def tp12589 : ℝ := (230591271 / 1000000000)
noncomputable def tm12589 : ℝ := (-((1207879271 / 2000000000)))
noncomputable def ep12589 : ℝ := (12777233840947479 / 25000000000000000000)
noncomputable def em12589 : ℝ := (49834439968844677 / 100000000000000000000)
noncomputable def bp12589 : ℝ := (699089935810790193 / 1562500000000000000)
noncomputable def bm12589 : ℝ := (45648145414547369631 / 100000000000000000000)

theorem positive12589 :
    Eplus aL (agent12589.root+dsL) scalar12589.worldRadius world12589.frame
      agent12589.frame tp12589 ≤ -ep12589 := by
  apply positive_check (eT := (3611256794252102327 / 3125000000000000000)) (y := (37779341481983524481 / 100000000000000000000)) (u := (729530745629053671 / 500000000000000000))
  · norm_num [world12589, agent12589, scalar12589, tp12589, tm12589, ep12589, em12589, dsL]
  · norm_num [world12589, agent12589, scalar12589, tp12589, tm12589, ep12589, em12589, dsL]
  · norm_num [world12589, agent12589, scalar12589, tp12589, tm12589, ep12589, em12589, dsL]
  · norm_num [world12589, agent12589, scalar12589, tp12589, tm12589, ep12589, em12589, dsL]
  · norm_num [world12589, agent12589, scalar12589, tp12589, tm12589, ep12589, em12589, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12589, agent12589, tp12589, tm12589, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12589, agent12589, scalar12589, tp12589, tm12589, ep12589, em12589, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12589, agent12589, tp12589, tm12589, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12589, agent12589, scalar12589, tp12589, tm12589, ep12589, em12589, dsL]

theorem negative12589 :
    Eminus aL (agent12589.root+dsL) scalar12589.worldRadius world12589.frame
      agent12589.frame tm12589 ≤ -em12589 := by
  apply negative_check (lo := (68469819715399812303 / 100000000000000000000)) (hi := (4279363732212488269 / 6250000000000000000))
    (y := (-((17924908562512210769 / 25000000000000000000)))) (u := (48821649095334400773 / 100000000000000000000))
  · norm_num [world12589, agent12589, scalar12589, tp12589, tm12589, ep12589, em12589, dsL]
  · norm_num [world12589, agent12589, scalar12589, tp12589, tm12589, ep12589, em12589, dsL]
  · norm_num [world12589, agent12589, scalar12589, tp12589, tm12589, ep12589, em12589, dsL]
  · norm_num [world12589, agent12589, scalar12589, tp12589, tm12589, ep12589, em12589, dsL]
  · norm_num [world12589, agent12589, scalar12589, tp12589, tm12589, ep12589, em12589, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12589, agent12589, tp12589, tm12589, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12589, agent12589, tp12589, tm12589, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12589, agent12589, scalar12589, tp12589, tm12589, ep12589, em12589, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12589, agent12589, tp12589, tm12589, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12589, agent12589, scalar12589, tp12589, tm12589, ep12589, em12589, dsL]

theorem tails12589 :
    exp (-((12589:ℝ)*ep12589)) ≤ scalar12589.upperTail ∧
    exp (-((12589:ℝ)*em12589)) ≤ scalar12589.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12589:ℝ)) (by norm_num [ep12589]) ?_)
      (show bp12589^8 ≤ scalar12589.upperTail by norm_num [bp12589, scalar12589])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12589, bp12589, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12589:ℝ)) (by norm_num [em12589]) ?_)
      (show bm12589^8 ≤ scalar12589.lowerTail by norm_num [bm12589, scalar12589])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12589, bm12589, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12589 :
    agent12589.root+dsL+scalar12589.worldRadius < √(1/100/aL) ∧
    2*(agent12589.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12589, agent12589, scalar12589, tp12589, tm12589, ep12589, em12589, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12589, agent12589, scalar12589, tp12589, tm12589, ep12589, em12589, dsL]

noncomputable def master12589 : MasterCertificate 12589 world12589 agent12589 :=
  master scalar12589 dsL tp12589 tm12589 ep12589 em12589
    (by norm_num [dsL]) (by norm_num [tp12589]) (by norm_num [tm12589])
    (by norm_num [ep12589]) (by norm_num [em12589])
    positive12589 negative12589 tails12589.1 tails12589.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12589.1 tailGuards12589.2

theorem preserves12589 : master12589.toScalarCertificate = scalar12589 := rfl

noncomputable def tp12590 : ℝ := (230607723 / 1000000000)
noncomputable def tm12590 : ℝ := (-((150995401 / 250000000)))
noncomputable def ep12590 : ℝ := (51113140626574077 / 100000000000000000000)
noncomputable def em12590 : ℝ := (49838387688747219 / 100000000000000000000)
noncomputable def bp12590 : ℝ := (44735936867081968617 / 100000000000000000000)
noncomputable def bm12590 : ℝ := (45642466212280279681 / 100000000000000000000)

theorem positive12590 :
    Eplus aL (agent12590.root+dsL) scalar12590.worldRadius world12590.frame
      agent12590.frame tp12590 ≤ -ep12590 := by
  apply positive_check (eT := (57780517130359849213 / 50000000000000000000)) (y := (1511178123316595857 / 4000000000000000000)) (u := (145906311958522948937 / 100000000000000000000))
  · norm_num [world12590, agent12590, scalar12590, tp12590, tm12590, ep12590, em12590, dsL]
  · norm_num [world12590, agent12590, scalar12590, tp12590, tm12590, ep12590, em12590, dsL]
  · norm_num [world12590, agent12590, scalar12590, tp12590, tm12590, ep12590, em12590, dsL]
  · norm_num [world12590, agent12590, scalar12590, tp12590, tm12590, ep12590, em12590, dsL]
  · norm_num [world12590, agent12590, scalar12590, tp12590, tm12590, ep12590, em12590, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12590, agent12590, tp12590, tm12590, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12590, agent12590, scalar12590, tp12590, tm12590, ep12590, em12590, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12590, agent12590, tp12590, tm12590, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12590, agent12590, scalar12590, tp12590, tm12590, ep12590, em12590, dsL]

theorem negative12590 :
    Eminus aL (agent12590.root+dsL) scalar12590.worldRadius world12590.frame
      agent12590.frame tm12590 ≤ -em12590 := by
  apply negative_check (lo := (6846860026321720459 / 10000000000000000000)) (hi := (68468600263217204591 / 100000000000000000000))
    (y := (-((71697839984639347863 / 100000000000000000000)))) (u := (24411262546577651467 / 50000000000000000000))
  · norm_num [world12590, agent12590, scalar12590, tp12590, tm12590, ep12590, em12590, dsL]
  · norm_num [world12590, agent12590, scalar12590, tp12590, tm12590, ep12590, em12590, dsL]
  · norm_num [world12590, agent12590, scalar12590, tp12590, tm12590, ep12590, em12590, dsL]
  · norm_num [world12590, agent12590, scalar12590, tp12590, tm12590, ep12590, em12590, dsL]
  · norm_num [world12590, agent12590, scalar12590, tp12590, tm12590, ep12590, em12590, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12590, agent12590, tp12590, tm12590, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12590, agent12590, tp12590, tm12590, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12590, agent12590, scalar12590, tp12590, tm12590, ep12590, em12590, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12590, agent12590, tp12590, tm12590, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12590, agent12590, scalar12590, tp12590, tm12590, ep12590, em12590, dsL]

theorem tails12590 :
    exp (-((12590:ℝ)*ep12590)) ≤ scalar12590.upperTail ∧
    exp (-((12590:ℝ)*em12590)) ≤ scalar12590.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12590:ℝ)) (by norm_num [ep12590]) ?_)
      (show bp12590^8 ≤ scalar12590.upperTail by norm_num [bp12590, scalar12590])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12590, bp12590, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12590:ℝ)) (by norm_num [em12590]) ?_)
      (show bm12590^8 ≤ scalar12590.lowerTail by norm_num [bm12590, scalar12590])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12590, bm12590, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12590 :
    agent12590.root+dsL+scalar12590.worldRadius < √(1/100/aL) ∧
    2*(agent12590.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12590, agent12590, scalar12590, tp12590, tm12590, ep12590, em12590, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12590, agent12590, scalar12590, tp12590, tm12590, ep12590, em12590, dsL]

noncomputable def master12590 : MasterCertificate 12590 world12590 agent12590 :=
  master scalar12590 dsL tp12590 tm12590 ep12590 em12590
    (by norm_num [dsL]) (by norm_num [tp12590]) (by norm_num [tm12590])
    (by norm_num [ep12590]) (by norm_num [em12590])
    positive12590 negative12590 tails12590.1 tails12590.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12590.1 tailGuards12590.2

theorem preserves12590 : master12590.toScalarCertificate = scalar12590 := rfl

noncomputable def tp12591 : ℝ := (2306166403 / 10000000000)
noncomputable def tm12591 : ℝ := (-((6040007721 / 10000000000)))
noncomputable def ep12591 : ℝ := (25557949641865689 / 50000000000000000000)
noncomputable def em12591 : ℝ := (1557523779762403 / 3125000000000000000)
noncomputable def bp12591 : ℝ := (44731136545210128231 / 100000000000000000000)
noncomputable def bm12591 : ℝ := (45637918158558010711 / 100000000000000000000)

theorem positive12591 :
    Eplus aL (agent12591.root+dsL) scalar12591.worldRadius world12591.frame
      agent12591.frame tp12591 ≤ -ep12591 := by
  apply positive_check (eT := (115561305046186643403 / 100000000000000000000)) (y := (37780293991197370743 / 100000000000000000000)) (u := (72953769450971794083 / 50000000000000000000))
  · norm_num [world12591, agent12591, scalar12591, tp12591, tm12591, ep12591, em12591, dsL]
  · norm_num [world12591, agent12591, scalar12591, tp12591, tm12591, ep12591, em12591, dsL]
  · norm_num [world12591, agent12591, scalar12591, tp12591, tm12591, ep12591, em12591, dsL]
  · norm_num [world12591, agent12591, scalar12591, tp12591, tm12591, ep12591, em12591, dsL]
  · norm_num [world12591, agent12591, scalar12591, tp12591, tm12591, ep12591, em12591, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12591, agent12591, tp12591, tm12591, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12591, agent12591, scalar12591, tp12591, tm12591, ep12591, em12591, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12591, agent12591, tp12591, tm12591, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12591, agent12591, scalar12591, tp12591, tm12591, ep12591, em12591, dsL]

theorem negative12591 :
    Eminus aL (agent12591.root+dsL) scalar12591.worldRadius world12591.frame
      agent12591.frame tm12591 ≤ -em12591 := by
  apply negative_check (lo := (13693671971643848027 / 20000000000000000000)) (hi := (8558544982277405017 / 12500000000000000000))
    (y := (-((35848982316909688653 / 50000000000000000000)))) (u := (4882246423631603343 / 10000000000000000000))
  · norm_num [world12591, agent12591, scalar12591, tp12591, tm12591, ep12591, em12591, dsL]
  · norm_num [world12591, agent12591, scalar12591, tp12591, tm12591, ep12591, em12591, dsL]
  · norm_num [world12591, agent12591, scalar12591, tp12591, tm12591, ep12591, em12591, dsL]
  · norm_num [world12591, agent12591, scalar12591, tp12591, tm12591, ep12591, em12591, dsL]
  · norm_num [world12591, agent12591, scalar12591, tp12591, tm12591, ep12591, em12591, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12591, agent12591, tp12591, tm12591, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12591, agent12591, tp12591, tm12591, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12591, agent12591, scalar12591, tp12591, tm12591, ep12591, em12591, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12591, agent12591, tp12591, tm12591, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12591, agent12591, scalar12591, tp12591, tm12591, ep12591, em12591, dsL]

theorem tails12591 :
    exp (-((12591:ℝ)*ep12591)) ≤ scalar12591.upperTail ∧
    exp (-((12591:ℝ)*em12591)) ≤ scalar12591.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12591:ℝ)) (by norm_num [ep12591]) ?_)
      (show bp12591^8 ≤ scalar12591.upperTail by norm_num [bp12591, scalar12591])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12591, bp12591, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12591:ℝ)) (by norm_num [em12591]) ?_)
      (show bm12591^8 ≤ scalar12591.lowerTail by norm_num [bm12591, scalar12591])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12591, bm12591, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12591 :
    agent12591.root+dsL+scalar12591.worldRadius < √(1/100/aL) ∧
    2*(agent12591.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12591, agent12591, scalar12591, tp12591, tm12591, ep12591, em12591, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12591, agent12591, scalar12591, tp12591, tm12591, ep12591, em12591, dsL]

noncomputable def master12591 : MasterCertificate 12591 world12591 agent12591 :=
  master scalar12591 dsL tp12591 tm12591 ep12591 em12591
    (by norm_num [dsL]) (by norm_num [tp12591]) (by norm_num [tm12591])
    (by norm_num [ep12591]) (by norm_num [em12591])
    positive12591 negative12591 tails12591.1 tails12591.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12591.1 tailGuards12591.2

theorem preserves12591 : master12591.toScalarCertificate = scalar12591 := rfl

noncomputable def tp12592 : ℝ := (2306255427 / 10000000000)
noncomputable def tm12592 : ℝ := (-((3020099629 / 5000000000)))
noncomputable def ep12592 : ℝ := (1022373119801261 / 2000000000000000000)
noncomputable def em12592 : ℝ := (24921566201631921 / 50000000000000000000)
noncomputable def bp12592 : ℝ := (894526756066693559 / 2000000000000000000)
noncomputable def bm12592 : ℝ := (713021431083494203 / 1562500000000000000)

theorem positive12592 :
    Eplus aL (agent12592.root+dsL) scalar12592.worldRadius world12592.frame
      agent12592.frame tp12592 ≤ -ep12592 := by
  apply positive_check (eT := (115561574784277577719 / 100000000000000000000)) (y := (295165100131115439 / 781250000000000000)) (u := (72954381408422090783 / 50000000000000000000))
  · norm_num [world12592, agent12592, scalar12592, tp12592, tm12592, ep12592, em12592, dsL]
  · norm_num [world12592, agent12592, scalar12592, tp12592, tm12592, ep12592, em12592, dsL]
  · norm_num [world12592, agent12592, scalar12592, tp12592, tm12592, ep12592, em12592, dsL]
  · norm_num [world12592, agent12592, scalar12592, tp12592, tm12592, ep12592, em12592, dsL]
  · norm_num [world12592, agent12592, scalar12592, tp12592, tm12592, ep12592, em12592, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12592, agent12592, tp12592, tm12592, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12592, agent12592, scalar12592, tp12592, tm12592, ep12592, em12592, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12592, agent12592, tp12592, tm12592, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12592, agent12592, scalar12592, tp12592, tm12592, ep12592, em12592, dsL]

theorem negative12592 :
    Eminus aL (agent12592.root+dsL) scalar12592.worldRadius world12592.frame
      agent12592.frame tm12592 ≤ -em12592 := by
  apply negative_check (lo := (68468120014909376379 / 100000000000000000000)) (hi := (3423406000745468819 / 5000000000000000000))
    (y := (-((4481130539909309101 / 6250000000000000000)))) (u := (610280046177360327 / 1250000000000000000))
  · norm_num [world12592, agent12592, scalar12592, tp12592, tm12592, ep12592, em12592, dsL]
  · norm_num [world12592, agent12592, scalar12592, tp12592, tm12592, ep12592, em12592, dsL]
  · norm_num [world12592, agent12592, scalar12592, tp12592, tm12592, ep12592, em12592, dsL]
  · norm_num [world12592, agent12592, scalar12592, tp12592, tm12592, ep12592, em12592, dsL]
  · norm_num [world12592, agent12592, scalar12592, tp12592, tm12592, ep12592, em12592, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12592, agent12592, tp12592, tm12592, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12592, agent12592, tp12592, tm12592, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12592, agent12592, scalar12592, tp12592, tm12592, ep12592, em12592, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12592, agent12592, tp12592, tm12592, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12592, agent12592, scalar12592, tp12592, tm12592, ep12592, em12592, dsL]

theorem tails12592 :
    exp (-((12592:ℝ)*ep12592)) ≤ scalar12592.upperTail ∧
    exp (-((12592:ℝ)*em12592)) ≤ scalar12592.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12592:ℝ)) (by norm_num [ep12592]) ?_)
      (show bp12592^8 ≤ scalar12592.upperTail by norm_num [bp12592, scalar12592])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12592, bp12592, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12592:ℝ)) (by norm_num [em12592]) ?_)
      (show bm12592^8 ≤ scalar12592.lowerTail by norm_num [bm12592, scalar12592])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12592, bm12592, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12592 :
    agent12592.root+dsL+scalar12592.worldRadius < √(1/100/aL) ∧
    2*(agent12592.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12592, agent12592, scalar12592, tp12592, tm12592, ep12592, em12592, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12592, agent12592, scalar12592, tp12592, tm12592, ep12592, em12592, dsL]

noncomputable def master12592 : MasterCertificate 12592 world12592 agent12592 :=
  master scalar12592 dsL tp12592 tm12592 ep12592 em12592
    (by norm_num [dsL]) (by norm_num [tp12592]) (by norm_num [tm12592])
    (by norm_num [ep12592]) (by norm_num [em12592])
    positive12592 negative12592 tails12592.1 tails12592.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12592.1 tailGuards12592.2

theorem preserves12592 : master12592.toScalarCertificate = scalar12592 := rfl

noncomputable def tp12593 : ℝ := (57658613 / 250000000)
noncomputable def tm12593 : ℝ := (-((1510097709 / 2500000000)))
noncomputable def ep12593 : ℝ := (51121412150806119 / 100000000000000000000)
noncomputable def em12593 : ℝ := (49845503334963579 / 100000000000000000000)
noncomputable def bp12593 : ℝ := (11180384913033984351 / 25000000000000000000)
noncomputable def bm12593 : ℝ := (22814412787724213559 / 50000000000000000000)

theorem positive12593 :
    Eplus aL (agent12593.root+dsL) scalar12593.worldRadius world12593.frame
      agent12593.frame tp12593 ≤ -ep12593 := by
  apply positive_check (eT := (2889046126373446629 / 2500000000000000000)) (y := (7556394629386516393 / 20000000000000000000)) (u := (145909988937321062907 / 100000000000000000000))
  · norm_num [world12593, agent12593, scalar12593, tp12593, tm12593, ep12593, em12593, dsL]
  · norm_num [world12593, agent12593, scalar12593, tp12593, tm12593, ep12593, em12593, dsL]
  · norm_num [world12593, agent12593, scalar12593, tp12593, tm12593, ep12593, em12593, dsL]
  · norm_num [world12593, agent12593, scalar12593, tp12593, tm12593, ep12593, em12593, dsL]
  · norm_num [world12593, agent12593, scalar12593, tp12593, tm12593, ep12593, em12593, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12593, agent12593, tp12593, tm12593, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12593, agent12593, scalar12593, tp12593, tm12593, ep12593, em12593, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12593, agent12593, tp12593, tm12593, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12593, agent12593, scalar12593, tp12593, tm12593, ep12593, em12593, dsL]

theorem negative12593 :
    Eminus aL (agent12593.root+dsL) scalar12593.worldRadius world12593.frame
      agent12593.frame tm12593 ≤ -em12593 := by
  apply negative_check (lo := (68467879938884906909 / 100000000000000000000)) (hi := (6846787993888490691 / 10000000000000000000))
    (y := (-((1120284590260962859 / 1562500000000000000)))) (u := (24411171299386488707 / 50000000000000000000))
  · norm_num [world12593, agent12593, scalar12593, tp12593, tm12593, ep12593, em12593, dsL]
  · norm_num [world12593, agent12593, scalar12593, tp12593, tm12593, ep12593, em12593, dsL]
  · norm_num [world12593, agent12593, scalar12593, tp12593, tm12593, ep12593, em12593, dsL]
  · norm_num [world12593, agent12593, scalar12593, tp12593, tm12593, ep12593, em12593, dsL]
  · norm_num [world12593, agent12593, scalar12593, tp12593, tm12593, ep12593, em12593, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12593, agent12593, tp12593, tm12593, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12593, agent12593, tp12593, tm12593, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12593, agent12593, scalar12593, tp12593, tm12593, ep12593, em12593, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12593, agent12593, tp12593, tm12593, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12593, agent12593, scalar12593, tp12593, tm12593, ep12593, em12593, dsL]

theorem tails12593 :
    exp (-((12593:ℝ)*ep12593)) ≤ scalar12593.upperTail ∧
    exp (-((12593:ℝ)*em12593)) ≤ scalar12593.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12593:ℝ)) (by norm_num [ep12593]) ?_)
      (show bp12593^8 ≤ scalar12593.upperTail by norm_num [bp12593, scalar12593])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12593, bp12593, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12593:ℝ)) (by norm_num [em12593]) ?_)
      (show bm12593^8 ≤ scalar12593.lowerTail by norm_num [bm12593, scalar12593])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12593, bm12593, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12593 :
    agent12593.root+dsL+scalar12593.worldRadius < √(1/100/aL) ∧
    2*(agent12593.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12593, agent12593, scalar12593, tp12593, tm12593, ep12593, em12593, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12593, agent12593, scalar12593, tp12593, tm12593, ep12593, em12593, dsL]

noncomputable def master12593 : MasterCertificate 12593 world12593 agent12593 :=
  master scalar12593 dsL tp12593 tm12593 ep12593 em12593
    (by norm_num [dsL]) (by norm_num [tp12593]) (by norm_num [tm12593])
    (by norm_num [ep12593]) (by norm_num [em12593])
    positive12593 negative12593 tails12593.1 tails12593.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12593.1 tailGuards12593.2

theorem preserves12593 : master12593.toScalarCertificate = scalar12593 := rfl

noncomputable def tp12594 : ℝ := (1153216749 / 5000000000)
noncomputable def tm12594 : ℝ := (-((377536387 / 625000000)))
noncomputable def ep12594 : ℝ := (25562083330389311 / 50000000000000000000)
noncomputable def em12594 : ℝ := (24923936385463809 / 50000000000000000000)
noncomputable def bp12594 : ℝ := (22358371434811129931 / 50000000000000000000)
noncomputable def bm12594 : ℝ := (45624280818296291241 / 100000000000000000000)

theorem positive12594 :
    Eplus aL (agent12594.root+dsL) scalar12594.worldRadius world12594.frame
      agent12594.frame tp12594 ≤ -ep12594 := by
  apply positive_check (eT := (28890528631168519411 / 25000000000000000000)) (y := (9445702947730090379 / 25000000000000000000)) (u := (72955606303900983923 / 50000000000000000000))
  · norm_num [world12594, agent12594, scalar12594, tp12594, tm12594, ep12594, em12594, dsL]
  · norm_num [world12594, agent12594, scalar12594, tp12594, tm12594, ep12594, em12594, dsL]
  · norm_num [world12594, agent12594, scalar12594, tp12594, tm12594, ep12594, em12594, dsL]
  · norm_num [world12594, agent12594, scalar12594, tp12594, tm12594, ep12594, em12594, dsL]
  · norm_num [world12594, agent12594, scalar12594, tp12594, tm12594, ep12594, em12594, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12594, agent12594, tp12594, tm12594, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12594, agent12594, scalar12594, tp12594, tm12594, ep12594, em12594, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12594, agent12594, tp12594, tm12594, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12594, agent12594, scalar12594, tp12594, tm12594, ep12594, em12594, dsL]

theorem negative12594 :
    Eminus aL (agent12594.root+dsL) scalar12594.worldRadius world12594.frame
      agent12594.frame tm12594 ≤ -em12594 := by
  apply negative_check (lo := (34233820379711433659 / 50000000000000000000)) (hi := (68467640759422867319 / 100000000000000000000))
    (y := (-((35849168672760275667 / 50000000000000000000)))) (u := (24411141134809064487 / 50000000000000000000))
  · norm_num [world12594, agent12594, scalar12594, tp12594, tm12594, ep12594, em12594, dsL]
  · norm_num [world12594, agent12594, scalar12594, tp12594, tm12594, ep12594, em12594, dsL]
  · norm_num [world12594, agent12594, scalar12594, tp12594, tm12594, ep12594, em12594, dsL]
  · norm_num [world12594, agent12594, scalar12594, tp12594, tm12594, ep12594, em12594, dsL]
  · norm_num [world12594, agent12594, scalar12594, tp12594, tm12594, ep12594, em12594, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12594, agent12594, tp12594, tm12594, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12594, agent12594, tp12594, tm12594, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12594, agent12594, scalar12594, tp12594, tm12594, ep12594, em12594, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12594, agent12594, tp12594, tm12594, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12594, agent12594, scalar12594, tp12594, tm12594, ep12594, em12594, dsL]

theorem tails12594 :
    exp (-((12594:ℝ)*ep12594)) ≤ scalar12594.upperTail ∧
    exp (-((12594:ℝ)*em12594)) ≤ scalar12594.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12594:ℝ)) (by norm_num [ep12594]) ?_)
      (show bp12594^8 ≤ scalar12594.upperTail by norm_num [bp12594, scalar12594])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12594, bp12594, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12594:ℝ)) (by norm_num [em12594]) ?_)
      (show bm12594^8 ≤ scalar12594.lowerTail by norm_num [bm12594, scalar12594])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12594, bm12594, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12594 :
    agent12594.root+dsL+scalar12594.worldRadius < √(1/100/aL) ∧
    2*(agent12594.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12594, agent12594, scalar12594, tp12594, tm12594, ep12594, em12594, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12594, agent12594, scalar12594, tp12594, tm12594, ep12594, em12594, dsL]

noncomputable def master12594 : MasterCertificate 12594 world12594 agent12594 :=
  master scalar12594 dsL tp12594 tm12594 ep12594 em12594
    (by norm_num [dsL]) (by norm_num [tp12594]) (by norm_num [tm12594])
    (by norm_num [ep12594]) (by norm_num [em12594])
    positive12594 negative12594 tails12594.1 tails12594.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12594.1 tailGuards12594.2

theorem preserves12594 : master12594.toScalarCertificate = scalar12594 := rfl

noncomputable def tp12595 : ℝ := (1153261249 / 5000000000)
noncomputable def tm12595 : ℝ := (-((120815473 / 200000000)))
noncomputable def ep12595 : ℝ := (25563459869934799 / 50000000000000000000)
noncomputable def em12595 : ℝ := (3115640062133571 / 6250000000000000000)
noncomputable def bp12595 : ℝ := (5588993412619139929 / 12500000000000000000)
noncomputable def bm12595 : ℝ := (2280986855730671017 / 5000000000000000000)

theorem positive12595 :
    Eplus aL (agent12595.root+dsL) scalar12595.worldRadius world12595.frame
      agent12595.frame tp12595 ≤ -ep12595 := by
  apply positive_check (eT := (14445298023294967217 / 12500000000000000000)) (y := (18891825173928651819 / 50000000000000000000)) (u := (145912436161527157087 / 100000000000000000000))
  · norm_num [world12595, agent12595, scalar12595, tp12595, tm12595, ep12595, em12595, dsL]
  · norm_num [world12595, agent12595, scalar12595, tp12595, tm12595, ep12595, em12595, dsL]
  · norm_num [world12595, agent12595, scalar12595, tp12595, tm12595, ep12595, em12595, dsL]
  · norm_num [world12595, agent12595, scalar12595, tp12595, tm12595, ep12595, em12595, dsL]
  · norm_num [world12595, agent12595, scalar12595, tp12595, tm12595, ep12595, em12595, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12595, agent12595, tp12595, tm12595, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12595, agent12595, scalar12595, tp12595, tm12595, ep12595, em12595, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12595, agent12595, tp12595, tm12595, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12595, agent12595, scalar12595, tp12595, tm12595, ep12595, em12595, dsL]

theorem negative12595 :
    Eminus aL (agent12595.root+dsL) scalar12595.worldRadius world12595.frame
      agent12595.frame tm12595 ≤ -em12595 := by
  apply negative_check (lo := (13693480217066733013 / 20000000000000000000)) (hi := (34233700542666832533 / 50000000000000000000))
    (y := (-((8962307566003262767 / 12500000000000000000)))) (u := (12205555532286150863 / 25000000000000000000))
  · norm_num [world12595, agent12595, scalar12595, tp12595, tm12595, ep12595, em12595, dsL]
  · norm_num [world12595, agent12595, scalar12595, tp12595, tm12595, ep12595, em12595, dsL]
  · norm_num [world12595, agent12595, scalar12595, tp12595, tm12595, ep12595, em12595, dsL]
  · norm_num [world12595, agent12595, scalar12595, tp12595, tm12595, ep12595, em12595, dsL]
  · norm_num [world12595, agent12595, scalar12595, tp12595, tm12595, ep12595, em12595, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12595, agent12595, tp12595, tm12595, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12595, agent12595, tp12595, tm12595, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12595, agent12595, scalar12595, tp12595, tm12595, ep12595, em12595, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12595, agent12595, tp12595, tm12595, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12595, agent12595, scalar12595, tp12595, tm12595, ep12595, em12595, dsL]

theorem tails12595 :
    exp (-((12595:ℝ)*ep12595)) ≤ scalar12595.upperTail ∧
    exp (-((12595:ℝ)*em12595)) ≤ scalar12595.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12595:ℝ)) (by norm_num [ep12595]) ?_)
      (show bp12595^8 ≤ scalar12595.upperTail by norm_num [bp12595, scalar12595])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12595, bp12595, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12595:ℝ)) (by norm_num [em12595]) ?_)
      (show bm12595^8 ≤ scalar12595.lowerTail by norm_num [bm12595, scalar12595])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12595, bm12595, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12595 :
    agent12595.root+dsL+scalar12595.worldRadius < √(1/100/aL) ∧
    2*(agent12595.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12595, agent12595, scalar12595, tp12595, tm12595, ep12595, em12595, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12595, agent12595, scalar12595, tp12595, tm12595, ep12595, em12595, dsL]

noncomputable def master12595 : MasterCertificate 12595 world12595 agent12595 :=
  master scalar12595 dsL tp12595 tm12595 ep12595 em12595
    (by norm_num [dsL]) (by norm_num [tp12595]) (by norm_num [tm12595])
    (by norm_num [ep12595]) (by norm_num [em12595])
    positive12595 negative12595 tails12595.1 tails12595.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12595.1 tailGuards12595.2

theorem preserves12595 : master12595.toScalarCertificate = scalar12595 := rfl

noncomputable def tp12596 : ℝ := (576652927 / 2500000000)
noncomputable def tm12596 : ℝ := (-((6040965673 / 10000000000)))
noncomputable def ep12596 : ℝ := (10225935408696467 / 20000000000000000000)
noncomputable def em12596 : ℝ := (12463153477255931 / 25000000000000000000)
noncomputable def bp12596 : ℝ := (44707148965170151639 / 100000000000000000000)
noncomputable def bm12596 : ℝ := (45615190223753758661 / 100000000000000000000)

theorem positive12596 :
    Eplus aL (agent12596.root+dsL) scalar12596.worldRadius world12596.frame
      agent12596.frame tp12596 ≤ -ep12596 := by
  apply positive_check (eT := (115562655402342796289 / 100000000000000000000)) (y := (37784485958285178413 / 100000000000000000000)) (u := (72956827713076716509 / 50000000000000000000))
  · norm_num [world12596, agent12596, scalar12596, tp12596, tm12596, ep12596, em12596, dsL]
  · norm_num [world12596, agent12596, scalar12596, tp12596, tm12596, ep12596, em12596, dsL]
  · norm_num [world12596, agent12596, scalar12596, tp12596, tm12596, ep12596, em12596, dsL]
  · norm_num [world12596, agent12596, scalar12596, tp12596, tm12596, ep12596, em12596, dsL]
  · norm_num [world12596, agent12596, scalar12596, tp12596, tm12596, ep12596, em12596, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12596, agent12596, tp12596, tm12596, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12596, agent12596, scalar12596, tp12596, tm12596, ep12596, em12596, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12596, agent12596, tp12596, tm12596, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12596, agent12596, scalar12596, tp12596, tm12596, ep12596, em12596, dsL]

theorem negative12596 :
    Eminus aL (agent12596.root+dsL) scalar12596.worldRadius world12596.frame
      agent12596.frame tm12596 ≤ -em12596 := by
  apply negative_check (lo := (34233579464413471093 / 50000000000000000000)) (hi := (68467158928826942187 / 100000000000000000000))
    (y := (-((35849287961057884227 / 50000000000000000000)))) (u := (24411082895609163991 / 50000000000000000000))
  · norm_num [world12596, agent12596, scalar12596, tp12596, tm12596, ep12596, em12596, dsL]
  · norm_num [world12596, agent12596, scalar12596, tp12596, tm12596, ep12596, em12596, dsL]
  · norm_num [world12596, agent12596, scalar12596, tp12596, tm12596, ep12596, em12596, dsL]
  · norm_num [world12596, agent12596, scalar12596, tp12596, tm12596, ep12596, em12596, dsL]
  · norm_num [world12596, agent12596, scalar12596, tp12596, tm12596, ep12596, em12596, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12596, agent12596, tp12596, tm12596, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12596, agent12596, tp12596, tm12596, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12596, agent12596, scalar12596, tp12596, tm12596, ep12596, em12596, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12596, agent12596, tp12596, tm12596, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12596, agent12596, scalar12596, tp12596, tm12596, ep12596, em12596, dsL]

theorem tails12596 :
    exp (-((12596:ℝ)*ep12596)) ≤ scalar12596.upperTail ∧
    exp (-((12596:ℝ)*em12596)) ≤ scalar12596.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12596:ℝ)) (by norm_num [ep12596]) ?_)
      (show bp12596^8 ≤ scalar12596.upperTail by norm_num [bp12596, scalar12596])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12596, bp12596, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12596:ℝ)) (by norm_num [em12596]) ?_)
      (show bm12596^8 ≤ scalar12596.lowerTail by norm_num [bm12596, scalar12596])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12596, bm12596, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12596 :
    agent12596.root+dsL+scalar12596.worldRadius < √(1/100/aL) ∧
    2*(agent12596.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12596, agent12596, scalar12596, tp12596, tm12596, ep12596, em12596, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12596, agent12596, scalar12596, tp12596, tm12596, ep12596, em12596, dsL]

noncomputable def master12596 : MasterCertificate 12596 world12596 agent12596 :=
  master scalar12596 dsL tp12596 tm12596 ep12596 em12596
    (by norm_num [dsL]) (by norm_num [tp12596]) (by norm_num [tm12596])
    (by norm_num [ep12596]) (by norm_num [em12596])
    positive12596 negative12596 tails12596.1 tails12596.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12596.1 tailGuards12596.2

theorem preserves12596 : master12596.toScalarCertificate = scalar12596 := rfl

noncomputable def tp12597 : ℝ := (461340173 / 2000000000)
noncomputable def tm12597 : ℝ := (-((6041157629 / 10000000000)))
noncomputable def ep12597 : ℝ := (12783108208414911 / 25000000000000000000)
noncomputable def em12597 : ℝ := (9970997094537787 / 20000000000000000000)
noncomputable def bp12597 : ℝ := (11175587975370569423 / 25000000000000000000)
noncomputable def bm12597 : ℝ := (45610644485947049207 / 100000000000000000000)

theorem positive12597 :
    Eplus aL (agent12597.root+dsL) scalar12597.worldRadius world12597.frame
      agent12597.frame tp12597 ≤ -ep12597 := by
  apply positive_check (eT := (115562926266671975731 / 100000000000000000000)) (y := (37785320820905422311 / 100000000000000000000)) (u := (72957436804902745179 / 50000000000000000000))
  · norm_num [world12597, agent12597, scalar12597, tp12597, tm12597, ep12597, em12597, dsL]
  · norm_num [world12597, agent12597, scalar12597, tp12597, tm12597, ep12597, em12597, dsL]
  · norm_num [world12597, agent12597, scalar12597, tp12597, tm12597, ep12597, em12597, dsL]
  · norm_num [world12597, agent12597, scalar12597, tp12597, tm12597, ep12597, em12597, dsL]
  · norm_num [world12597, agent12597, scalar12597, tp12597, tm12597, ep12597, em12597, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12597, agent12597, tp12597, tm12597, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12597, agent12597, scalar12597, tp12597, tm12597, ep12597, em12597, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12597, agent12597, tp12597, tm12597, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12597, agent12597, scalar12597, tp12597, tm12597, ep12597, em12597, dsL]

theorem negative12597 :
    Eminus aL (agent12597.root+dsL) scalar12597.worldRadius world12597.frame
      agent12597.frame tm12597 ≤ -em12597 := by
  apply negative_check (lo := (17116729250875268361 / 25000000000000000000)) (hi := (13693383400700214689 / 20000000000000000000))
    (y := (-((2867947638841196691 / 4000000000000000000)))) (u := (24411054810939516181 / 50000000000000000000))
  · norm_num [world12597, agent12597, scalar12597, tp12597, tm12597, ep12597, em12597, dsL]
  · norm_num [world12597, agent12597, scalar12597, tp12597, tm12597, ep12597, em12597, dsL]
  · norm_num [world12597, agent12597, scalar12597, tp12597, tm12597, ep12597, em12597, dsL]
  · norm_num [world12597, agent12597, scalar12597, tp12597, tm12597, ep12597, em12597, dsL]
  · norm_num [world12597, agent12597, scalar12597, tp12597, tm12597, ep12597, em12597, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12597, agent12597, tp12597, tm12597, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12597, agent12597, tp12597, tm12597, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12597, agent12597, scalar12597, tp12597, tm12597, ep12597, em12597, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12597, agent12597, tp12597, tm12597, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12597, agent12597, scalar12597, tp12597, tm12597, ep12597, em12597, dsL]

theorem tails12597 :
    exp (-((12597:ℝ)*ep12597)) ≤ scalar12597.upperTail ∧
    exp (-((12597:ℝ)*em12597)) ≤ scalar12597.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12597:ℝ)) (by norm_num [ep12597]) ?_)
      (show bp12597^8 ≤ scalar12597.upperTail by norm_num [bp12597, scalar12597])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12597, bp12597, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12597:ℝ)) (by norm_num [em12597]) ?_)
      (show bm12597^8 ≤ scalar12597.lowerTail by norm_num [bm12597, scalar12597])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12597, bm12597, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12597 :
    agent12597.root+dsL+scalar12597.worldRadius < √(1/100/aL) ∧
    2*(agent12597.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12597, agent12597, scalar12597, tp12597, tm12597, ep12597, em12597, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12597, agent12597, scalar12597, tp12597, tm12597, ep12597, em12597, dsL]

noncomputable def master12597 : MasterCertificate 12597 world12597 agent12597 :=
  master scalar12597 dsL tp12597 tm12597 ep12597 em12597
    (by norm_num [dsL]) (by norm_num [tp12597]) (by norm_num [tm12597])
    (by norm_num [ep12597]) (by norm_num [em12597])
    positive12597 negative12597 tails12597.1 tails12597.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12597.1 tailGuards12597.2

theorem preserves12597 : master12597.toScalarCertificate = scalar12597 := rfl

noncomputable def tp12598 : ℝ := (461358011 / 2000000000)
noncomputable def tm12598 : ℝ := (-((1510337367 / 2500000000)))
noncomputable def ep12598 : ℝ := (25567593505602387 / 50000000000000000000)
noncomputable def em12598 : ℝ := (12464338879765419 / 25000000000000000000)
noncomputable def bp12598 : ℝ := (4469755617966627427 / 10000000000000000000)
noncomputable def bm12598 : ℝ := (45606100020439258767 / 100000000000000000000)

theorem positive12598 :
    Eplus aL (agent12598.root+dsL) scalar12598.worldRadius world12598.frame
      agent12598.frame tp12598 ≤ -ep12598 := by
  apply positive_check (eT := (28890799350641914079 / 25000000000000000000)) (y := (37786156904457987079 / 100000000000000000000)) (u := (29183218717032897433 / 20000000000000000000))
  · norm_num [world12598, agent12598, scalar12598, tp12598, tm12598, ep12598, em12598, dsL]
  · norm_num [world12598, agent12598, scalar12598, tp12598, tm12598, ep12598, em12598, dsL]
  · norm_num [world12598, agent12598, scalar12598, tp12598, tm12598, ep12598, em12598, dsL]
  · norm_num [world12598, agent12598, scalar12598, tp12598, tm12598, ep12598, em12598, dsL]
  · norm_num [world12598, agent12598, scalar12598, tp12598, tm12598, ep12598, em12598, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12598, agent12598, tp12598, tm12598, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12598, agent12598, scalar12598, tp12598, tm12598, ep12598, em12598, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12598, agent12598, tp12598, tm12598, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12598, agent12598, scalar12598, tp12598, tm12598, ep12598, em12598, dsL]

theorem negative12598 :
    Eminus aL (agent12598.root+dsL) scalar12598.worldRadius world12598.frame
      agent12598.frame tm12598 ≤ -em12598 := by
  apply negative_check (lo := (68466675523985523433 / 100000000000000000000)) (hi := (34233337761992761717 / 50000000000000000000))
    (y := (-((35849403026377676177 / 50000000000000000000)))) (u := (48822053436585215207 / 100000000000000000000))
  · norm_num [world12598, agent12598, scalar12598, tp12598, tm12598, ep12598, em12598, dsL]
  · norm_num [world12598, agent12598, scalar12598, tp12598, tm12598, ep12598, em12598, dsL]
  · norm_num [world12598, agent12598, scalar12598, tp12598, tm12598, ep12598, em12598, dsL]
  · norm_num [world12598, agent12598, scalar12598, tp12598, tm12598, ep12598, em12598, dsL]
  · norm_num [world12598, agent12598, scalar12598, tp12598, tm12598, ep12598, em12598, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12598, agent12598, tp12598, tm12598, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12598, agent12598, tp12598, tm12598, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12598, agent12598, scalar12598, tp12598, tm12598, ep12598, em12598, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12598, agent12598, tp12598, tm12598, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12598, agent12598, scalar12598, tp12598, tm12598, ep12598, em12598, dsL]

theorem tails12598 :
    exp (-((12598:ℝ)*ep12598)) ≤ scalar12598.upperTail ∧
    exp (-((12598:ℝ)*em12598)) ≤ scalar12598.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12598:ℝ)) (by norm_num [ep12598]) ?_)
      (show bp12598^8 ≤ scalar12598.upperTail by norm_num [bp12598, scalar12598])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12598, bp12598, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12598:ℝ)) (by norm_num [em12598]) ?_)
      (show bm12598^8 ≤ scalar12598.lowerTail by norm_num [bm12598, scalar12598])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12598, bm12598, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12598 :
    agent12598.root+dsL+scalar12598.worldRadius < √(1/100/aL) ∧
    2*(agent12598.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12598, agent12598, scalar12598, tp12598, tm12598, ep12598, em12598, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12598, agent12598, scalar12598, tp12598, tm12598, ep12598, em12598, dsL]

noncomputable def master12598 : MasterCertificate 12598 world12598 agent12598 :=
  master scalar12598 dsL tp12598 tm12598 ep12598 em12598
    (by norm_num [dsL]) (by norm_num [tp12598]) (by norm_num [tm12598])
    (by norm_num [ep12598]) (by norm_num [em12598])
    positive12598 negative12598 tails12598.1 tails12598.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12598.1 tailGuards12598.2

theorem preserves12598 : master12598.toScalarCertificate = scalar12598 := rfl

noncomputable def tp12599 : ℝ := (230687911 / 1000000000)
noncomputable def tm12599 : ℝ := (-((6041541227 / 10000000000)))
noncomputable def ep12599 : ℝ := (12784485043624329 / 25000000000000000000)
noncomputable def em12599 : ℝ := (49859724612972691 / 100000000000000000000)
noncomputable def bp12599 : ℝ := (44692761378498428731 / 100000000000000000000)
noncomputable def bm12599 : ℝ := (45601556421556723223 / 100000000000000000000)

theorem positive12599 :
    Eplus aL (agent12599.root+dsL) scalar12599.worldRadius world12599.frame
      agent12599.frame tp12599 ≤ -ep12599 := by
  apply positive_check (eT := (57781733796313099701 / 50000000000000000000)) (y := (4723373868836852663 / 12500000000000000000)) (u := (29183462119585437451 / 20000000000000000000))
  · norm_num [world12599, agent12599, scalar12599, tp12599, tm12599, ep12599, em12599, dsL]
  · norm_num [world12599, agent12599, scalar12599, tp12599, tm12599, ep12599, em12599, dsL]
  · norm_num [world12599, agent12599, scalar12599, tp12599, tm12599, ep12599, em12599, dsL]
  · norm_num [world12599, agent12599, scalar12599, tp12599, tm12599, ep12599, em12599, dsL]
  · norm_num [world12599, agent12599, scalar12599, tp12599, tm12599, ep12599, em12599, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12599, agent12599, tp12599, tm12599, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12599, agent12599, scalar12599, tp12599, tm12599, ep12599, em12599, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12599, agent12599, tp12599, tm12599, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12599, agent12599, scalar12599, tp12599, tm12599, ep12599, em12599, dsL]

theorem negative12599 :
    Eminus aL (agent12599.root+dsL) scalar12599.worldRadius world12599.frame
      agent12599.frame tm12599 ≤ -em12599 := by
  apply negative_check (lo := (34233217165714828149 / 50000000000000000000)) (hi := (68466434331429656299 / 100000000000000000000))
    (y := (-((35849460477946229253 / 50000000000000000000)))) (u := (24410998669273223069 / 50000000000000000000))
  · norm_num [world12599, agent12599, scalar12599, tp12599, tm12599, ep12599, em12599, dsL]
  · norm_num [world12599, agent12599, scalar12599, tp12599, tm12599, ep12599, em12599, dsL]
  · norm_num [world12599, agent12599, scalar12599, tp12599, tm12599, ep12599, em12599, dsL]
  · norm_num [world12599, agent12599, scalar12599, tp12599, tm12599, ep12599, em12599, dsL]
  · norm_num [world12599, agent12599, scalar12599, tp12599, tm12599, ep12599, em12599, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12599, agent12599, tp12599, tm12599, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12599, agent12599, tp12599, tm12599, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12599, agent12599, scalar12599, tp12599, tm12599, ep12599, em12599, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12599, agent12599, tp12599, tm12599, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12599, agent12599, scalar12599, tp12599, tm12599, ep12599, em12599, dsL]

theorem tails12599 :
    exp (-((12599:ℝ)*ep12599)) ≤ scalar12599.upperTail ∧
    exp (-((12599:ℝ)*em12599)) ≤ scalar12599.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12599:ℝ)) (by norm_num [ep12599]) ?_)
      (show bp12599^8 ≤ scalar12599.upperTail by norm_num [bp12599, scalar12599])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12599, bp12599, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12599:ℝ)) (by norm_num [em12599]) ?_)
      (show bm12599^8 ≤ scalar12599.lowerTail by norm_num [bm12599, scalar12599])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12599, bm12599, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12599 :
    agent12599.root+dsL+scalar12599.worldRadius < √(1/100/aL) ∧
    2*(agent12599.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12599, agent12599, scalar12599, tp12599, tm12599, ep12599, em12599, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12599, agent12599, scalar12599, tp12599, tm12599, ep12599, em12599, dsL]

noncomputable def master12599 : MasterCertificate 12599 world12599 agent12599 :=
  master scalar12599 dsL tp12599 tm12599 ep12599 em12599
    (by norm_num [dsL]) (by norm_num [tp12599]) (by norm_num [tm12599])
    (by norm_num [ep12599]) (by norm_num [em12599])
    positive12599 negative12599 tails12599.1 tails12599.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12599.1 tailGuards12599.2

theorem preserves12599 : master12599.toScalarCertificate = scalar12599 := rfl

end BstLean.Part268
