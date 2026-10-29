import BstLean.Part261Checker
import BstLean.Part268Scalar12
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12650 : ℝ := (115590839 / 500000000)
noncomputable def tm12650 : ℝ := (-((6052549721 / 10000000000)))
noncomputable def ep12650 : ℝ := (51285128812885477 / 100000000000000000000)
noncomputable def em12650 : ℝ := (24994117802221693 / 50000000000000000000)
noncomputable def bp12650 : ℝ := (11110934633207927981 / 25000000000000000000)
noncomputable def bm12650 : ℝ := (45364561226000658463 / 100000000000000000000)

theorem positive12650 :
    Eplus aL (agent12650.root+dsL) scalar12650.worldRadius world12650.frame
      agent12650.frame tp12650 ≤ -ep12650 := by
  apply positive_check (eT := (11558015576568060719 / 10000000000000000000)) (y := (4728087802752767703 / 12500000000000000000)) (u := (145972348539831490963 / 100000000000000000000))
  · norm_num [world12650, agent12650, scalar12650, tp12650, tm12650, ep12650, em12650, dsL]
  · norm_num [world12650, agent12650, scalar12650, tp12650, tm12650, ep12650, em12650, dsL]
  · norm_num [world12650, agent12650, scalar12650, tp12650, tm12650, ep12650, em12650, dsL]
  · norm_num [world12650, agent12650, scalar12650, tp12650, tm12650, ep12650, em12650, dsL]
  · norm_num [world12650, agent12650, scalar12650, tp12650, tm12650, ep12650, em12650, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12650, agent12650, tp12650, tm12650, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12650, agent12650, scalar12650, tp12650, tm12650, ep12650, em12650, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12650, agent12650, tp12650, tm12650, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12650, agent12650, scalar12650, tp12650, tm12650, ep12650, em12650, dsL]

theorem negative12650 :
    Eminus aL (agent12650.root+dsL) scalar12650.worldRadius world12650.frame
      agent12650.frame tm12650 ≤ -em12650 := by
  apply negative_check (lo := (34224395411158472971 / 50000000000000000000)) (hi := (68448790822316945943 / 100000000000000000000))
    (y := (-((71692866581320682007 / 100000000000000000000)))) (u := (48824953294620168001 / 100000000000000000000))
  · norm_num [world12650, agent12650, scalar12650, tp12650, tm12650, ep12650, em12650, dsL]
  · norm_num [world12650, agent12650, scalar12650, tp12650, tm12650, ep12650, em12650, dsL]
  · norm_num [world12650, agent12650, scalar12650, tp12650, tm12650, ep12650, em12650, dsL]
  · norm_num [world12650, agent12650, scalar12650, tp12650, tm12650, ep12650, em12650, dsL]
  · norm_num [world12650, agent12650, scalar12650, tp12650, tm12650, ep12650, em12650, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12650, agent12650, tp12650, tm12650, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12650, agent12650, tp12650, tm12650, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12650, agent12650, scalar12650, tp12650, tm12650, ep12650, em12650, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12650, agent12650, tp12650, tm12650, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12650, agent12650, scalar12650, tp12650, tm12650, ep12650, em12650, dsL]

theorem tails12650 :
    exp (-((12650:ℝ)*ep12650)) ≤ scalar12650.upperTail ∧
    exp (-((12650:ℝ)*em12650)) ≤ scalar12650.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12650:ℝ)) (by norm_num [ep12650]) ?_)
      (show bp12650^8 ≤ scalar12650.upperTail by norm_num [bp12650, scalar12650])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12650, bp12650, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12650:ℝ)) (by norm_num [em12650]) ?_)
      (show bm12650^8 ≤ scalar12650.lowerTail by norm_num [bm12650, scalar12650])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12650, bm12650, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12650 :
    agent12650.root+dsL+scalar12650.worldRadius < √(1/100/aL) ∧
    2*(agent12650.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12650, agent12650, scalar12650, tp12650, tm12650, ep12650, em12650, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12650, agent12650, scalar12650, tp12650, tm12650, ep12650, em12650, dsL]

noncomputable def master12650 : MasterCertificate 12650 world12650 agent12650 :=
  master scalar12650 dsL tp12650 tm12650 ep12650 em12650
    (by norm_num [dsL]) (by norm_num [tp12650]) (by norm_num [tm12650])
    (by norm_num [ep12650]) (by norm_num [em12650])
    positive12650 negative12650 tails12650.1 tails12650.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12650.1 tailGuards12650.2

theorem preserves12650 : master12650.toScalarCertificate = scalar12650 := rfl

noncomputable def tp12651 : ℝ := (577975981 / 2500000000)
noncomputable def tm12651 : ℝ := (-((3026368503 / 5000000000)))
noncomputable def ep12651 : ℝ := (10257562886339763 / 20000000000000000000)
noncomputable def em12651 : ℝ := (499905430712929 / 1000000000000000000)
noncomputable def bp12651 : ℝ := (11109750536054220911 / 25000000000000000000)
noncomputable def bm12651 : ℝ := (22680035745407731703 / 50000000000000000000)

theorem positive12651 :
    Eplus aL (agent12651.root+dsL) scalar12651.worldRadius world12651.frame
      agent12651.frame tp12651 ≤ -ep12651 := by
  apply positive_check (eT := (7223775858815917329 / 6250000000000000000)) (y := (37825516452998886653 / 100000000000000000000)) (u := (36493384201200625831 / 25000000000000000000))
  · norm_num [world12651, agent12651, scalar12651, tp12651, tm12651, ep12651, em12651, dsL]
  · norm_num [world12651, agent12651, scalar12651, tp12651, tm12651, ep12651, em12651, dsL]
  · norm_num [world12651, agent12651, scalar12651, tp12651, tm12651, ep12651, em12651, dsL]
  · norm_num [world12651, agent12651, scalar12651, tp12651, tm12651, ep12651, em12651, dsL]
  · norm_num [world12651, agent12651, scalar12651, tp12651, tm12651, ep12651, em12651, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12651, agent12651, tp12651, tm12651, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12651, agent12651, scalar12651, tp12651, tm12651, ep12651, em12651, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12651, agent12651, tp12651, tm12651, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12651, agent12651, scalar12651, tp12651, tm12651, ep12651, em12651, dsL]

theorem negative12651 :
    Eminus aL (agent12651.root+dsL) scalar12651.worldRadius world12651.frame
      agent12651.frame tm12651 ≤ -em12651 := by
  apply negative_check (lo := (6844856602900252291 / 10000000000000000000)) (hi := (68448566029002522911 / 100000000000000000000))
    (y := (-((71692960275616901287 / 100000000000000000000)))) (u := (12206226887111307499 / 25000000000000000000))
  · norm_num [world12651, agent12651, scalar12651, tp12651, tm12651, ep12651, em12651, dsL]
  · norm_num [world12651, agent12651, scalar12651, tp12651, tm12651, ep12651, em12651, dsL]
  · norm_num [world12651, agent12651, scalar12651, tp12651, tm12651, ep12651, em12651, dsL]
  · norm_num [world12651, agent12651, scalar12651, tp12651, tm12651, ep12651, em12651, dsL]
  · norm_num [world12651, agent12651, scalar12651, tp12651, tm12651, ep12651, em12651, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12651, agent12651, tp12651, tm12651, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12651, agent12651, tp12651, tm12651, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12651, agent12651, scalar12651, tp12651, tm12651, ep12651, em12651, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12651, agent12651, tp12651, tm12651, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12651, agent12651, scalar12651, tp12651, tm12651, ep12651, em12651, dsL]

theorem tails12651 :
    exp (-((12651:ℝ)*ep12651)) ≤ scalar12651.upperTail ∧
    exp (-((12651:ℝ)*em12651)) ≤ scalar12651.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12651:ℝ)) (by norm_num [ep12651]) ?_)
      (show bp12651^8 ≤ scalar12651.upperTail by norm_num [bp12651, scalar12651])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12651, bp12651, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12651:ℝ)) (by norm_num [em12651]) ?_)
      (show bm12651^8 ≤ scalar12651.lowerTail by norm_num [bm12651, scalar12651])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12651, bm12651, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12651 :
    agent12651.root+dsL+scalar12651.worldRadius < √(1/100/aL) ∧
    2*(agent12651.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12651, agent12651, scalar12651, tp12651, tm12651, ep12651, em12651, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12651, agent12651, scalar12651, tp12651, tm12651, ep12651, em12651, dsL]

noncomputable def master12651 : MasterCertificate 12651 world12651 agent12651 :=
  master scalar12651 dsL tp12651 tm12651 ep12651 em12651
    (by norm_num [dsL]) (by norm_num [tp12651]) (by norm_num [tm12651])
    (by norm_num [ep12651]) (by norm_num [em12651])
    positive12651 negative12651 tails12651.1 tails12651.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12651.1 tailGuards12651.2

theorem preserves12651 : master12651.toScalarCertificate = scalar12651 := rfl

noncomputable def tp12652 : ℝ := (2311991029 / 10000000000)
noncomputable def tm12652 : ℝ := (-((121058483 / 200000000)))
noncomputable def ep12652 : ℝ := (51290497978166933 / 100000000000000000000)
noncomputable def em12652 : ℝ := (6249106081465513 / 12500000000000000000)
noncomputable def bp12652 : ℝ := (1777370696732886673 / 4000000000000000000)
noncomputable def bm12652 : ℝ := (45355583291463653643 / 100000000000000000000)

theorem positive12652 :
    Eplus aL (agent12652.root+dsL) scalar12652.worldRadius world12652.frame
      agent12652.frame tp12652 ≤ -ep12652 := by
  apply positive_check (eT := (5779033573334116661 / 5000000000000000000)) (y := (1891316508660004727 / 5000000000000000000)) (u := (72987362312896332377 / 50000000000000000000))
  · norm_num [world12652, agent12652, scalar12652, tp12652, tm12652, ep12652, em12652, dsL]
  · norm_num [world12652, agent12652, scalar12652, tp12652, tm12652, ep12652, em12652, dsL]
  · norm_num [world12652, agent12652, scalar12652, tp12652, tm12652, ep12652, em12652, dsL]
  · norm_num [world12652, agent12652, scalar12652, tp12652, tm12652, ep12652, em12652, dsL]
  · norm_num [world12652, agent12652, scalar12652, tp12652, tm12652, ep12652, em12652, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12652, agent12652, tp12652, tm12652, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12652, agent12652, scalar12652, tp12652, tm12652, ep12652, em12652, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12652, agent12652, tp12652, tm12652, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12652, agent12652, scalar12652, tp12652, tm12652, ep12652, em12652, dsL]

theorem negative12652 :
    Eminus aL (agent12652.root+dsL) scalar12652.worldRadius world12652.frame
      agent12652.frame tm12652 ≤ -em12652 := by
  apply negative_check (lo := (68448341783473147709 / 100000000000000000000)) (hi := (6844834178347314771 / 10000000000000000000))
    (y := (-((560101976908303351 / 781250000000000000)))) (u := (9764972450852126257 / 20000000000000000000))
  · norm_num [world12652, agent12652, scalar12652, tp12652, tm12652, ep12652, em12652, dsL]
  · norm_num [world12652, agent12652, scalar12652, tp12652, tm12652, ep12652, em12652, dsL]
  · norm_num [world12652, agent12652, scalar12652, tp12652, tm12652, ep12652, em12652, dsL]
  · norm_num [world12652, agent12652, scalar12652, tp12652, tm12652, ep12652, em12652, dsL]
  · norm_num [world12652, agent12652, scalar12652, tp12652, tm12652, ep12652, em12652, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12652, agent12652, tp12652, tm12652, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12652, agent12652, tp12652, tm12652, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12652, agent12652, scalar12652, tp12652, tm12652, ep12652, em12652, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12652, agent12652, tp12652, tm12652, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12652, agent12652, scalar12652, tp12652, tm12652, ep12652, em12652, dsL]

theorem tails12652 :
    exp (-((12652:ℝ)*ep12652)) ≤ scalar12652.upperTail ∧
    exp (-((12652:ℝ)*em12652)) ≤ scalar12652.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12652:ℝ)) (by norm_num [ep12652]) ?_)
      (show bp12652^8 ≤ scalar12652.upperTail by norm_num [bp12652, scalar12652])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12652, bp12652, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12652:ℝ)) (by norm_num [em12652]) ?_)
      (show bm12652^8 ≤ scalar12652.lowerTail by norm_num [bm12652, scalar12652])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12652, bm12652, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12652 :
    agent12652.root+dsL+scalar12652.worldRadius < √(1/100/aL) ∧
    2*(agent12652.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12652, agent12652, scalar12652, tp12652, tm12652, ep12652, em12652, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12652, agent12652, scalar12652, tp12652, tm12652, ep12652, em12652, dsL]

noncomputable def master12652 : MasterCertificate 12652 world12652 agent12652 :=
  master scalar12652 dsL tp12652 tm12652 ep12652 em12652
    (by norm_num [dsL]) (by norm_num [tp12652]) (by norm_num [tm12652])
    (by norm_num [ep12652]) (by norm_num [em12652])
    positive12652 negative12652 tails12652.1 tails12652.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12652.1 tailGuards12652.2

theorem preserves12652 : master12652.toScalarCertificate = scalar12652 := rfl

noncomputable def tp12653 : ℝ := (2312078041 / 10000000000)
noncomputable def tm12653 : ℝ := (-((3026555579 / 5000000000)))
noncomputable def ep12653 : ℝ := (51293180262956103 / 100000000000000000000)
noncomputable def em12653 : ℝ := (24997576508395391 / 50000000000000000000)
noncomputable def bp12653 : ℝ := (22214766892703372743 / 50000000000000000000)
noncomputable def bm12653 : ℝ := (45351096146561745509 / 100000000000000000000)

theorem positive12653 :
    Eplus aL (agent12653.root+dsL) scalar12653.worldRadius world12653.frame
      agent12653.frame tp12653 ≤ -ep12653 := by
  apply positive_check (eT := (115580928551703152431 / 100000000000000000000)) (y := (9456785722448254653 / 25000000000000000000)) (u := (145975910991422062423 / 100000000000000000000))
  · norm_num [world12653, agent12653, scalar12653, tp12653, tm12653, ep12653, em12653, dsL]
  · norm_num [world12653, agent12653, scalar12653, tp12653, tm12653, ep12653, em12653, dsL]
  · norm_num [world12653, agent12653, scalar12653, tp12653, tm12653, ep12653, em12653, dsL]
  · norm_num [world12653, agent12653, scalar12653, tp12653, tm12653, ep12653, em12653, dsL]
  · norm_num [world12653, agent12653, scalar12653, tp12653, tm12653, ep12653, em12653, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12653, agent12653, tp12653, tm12653, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12653, agent12653, scalar12653, tp12653, tm12653, ep12653, em12653, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12653, agent12653, tp12653, tm12653, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12653, agent12653, scalar12653, tp12653, tm12653, ep12653, em12653, dsL]

theorem negative12653 :
    Eminus aL (agent12653.root+dsL) scalar12653.worldRadius world12653.frame
      agent12653.frame tm12653 ≤ -em12653 := by
  apply negative_check (lo := (34224059032120283261 / 50000000000000000000)) (hi := (68448118064240566523 / 100000000000000000000))
    (y := (-((7169314564516368187 / 10000000000000000000)))) (u := (24412408521009638553 / 50000000000000000000))
  · norm_num [world12653, agent12653, scalar12653, tp12653, tm12653, ep12653, em12653, dsL]
  · norm_num [world12653, agent12653, scalar12653, tp12653, tm12653, ep12653, em12653, dsL]
  · norm_num [world12653, agent12653, scalar12653, tp12653, tm12653, ep12653, em12653, dsL]
  · norm_num [world12653, agent12653, scalar12653, tp12653, tm12653, ep12653, em12653, dsL]
  · norm_num [world12653, agent12653, scalar12653, tp12653, tm12653, ep12653, em12653, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12653, agent12653, tp12653, tm12653, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12653, agent12653, tp12653, tm12653, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12653, agent12653, scalar12653, tp12653, tm12653, ep12653, em12653, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12653, agent12653, tp12653, tm12653, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12653, agent12653, scalar12653, tp12653, tm12653, ep12653, em12653, dsL]

theorem tails12653 :
    exp (-((12653:ℝ)*ep12653)) ≤ scalar12653.upperTail ∧
    exp (-((12653:ℝ)*em12653)) ≤ scalar12653.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12653:ℝ)) (by norm_num [ep12653]) ?_)
      (show bp12653^8 ≤ scalar12653.upperTail by norm_num [bp12653, scalar12653])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12653, bp12653, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12653:ℝ)) (by norm_num [em12653]) ?_)
      (show bm12653^8 ≤ scalar12653.lowerTail by norm_num [bm12653, scalar12653])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12653, bm12653, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12653 :
    agent12653.root+dsL+scalar12653.worldRadius < √(1/100/aL) ∧
    2*(agent12653.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12653, agent12653, scalar12653, tp12653, tm12653, ep12653, em12653, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12653, agent12653, scalar12653, tp12653, tm12653, ep12653, em12653, dsL]

noncomputable def master12653 : MasterCertificate 12653 world12653 agent12653 :=
  master scalar12653 dsL tp12653 tm12653 ep12653 em12653
    (by norm_num [dsL]) (by norm_num [tp12653]) (by norm_num [tm12653])
    (by norm_num [ep12653]) (by norm_num [em12653])
    positive12653 negative12653 tails12653.1 tails12653.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12653.1 tailGuards12653.2

theorem preserves12653 : master12653.toScalarCertificate = scalar12653 := rfl

noncomputable def tp12654 : ℝ := (289020631 / 1250000000)
noncomputable def tm12654 : ℝ := (-((6053298019 / 10000000000)))
noncomputable def ep12654 : ℝ := (51295861399505069 / 100000000000000000000)
noncomputable def em12654 : ℝ := (49997456344967491 / 100000000000000000000)
noncomputable def bp12654 : ℝ := (44424801165726781091 / 100000000000000000000)
noncomputable def bm12654 : ℝ := (45346609928076870873 / 100000000000000000000)

theorem positive12654 :
    Eplus aL (agent12654.root+dsL) scalar12654.worldRadius world12654.frame
      agent12654.frame tp12654 ≤ -ep12654 := by
  apply positive_check (eT := (115581185633148668609 / 100000000000000000000)) (y := (18913977846556944783 / 50000000000000000000)) (u := (29195419498659245823 / 20000000000000000000))
  · norm_num [world12654, agent12654, scalar12654, tp12654, tm12654, ep12654, em12654, dsL]
  · norm_num [world12654, agent12654, scalar12654, tp12654, tm12654, ep12654, em12654, dsL]
  · norm_num [world12654, agent12654, scalar12654, tp12654, tm12654, ep12654, em12654, dsL]
  · norm_num [world12654, agent12654, scalar12654, tp12654, tm12654, ep12654, em12654, dsL]
  · norm_num [world12654, agent12654, scalar12654, tp12654, tm12654, ep12654, em12654, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12654, agent12654, tp12654, tm12654, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12654, agent12654, scalar12654, tp12654, tm12654, ep12654, em12654, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12654, agent12654, tp12654, tm12654, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12654, agent12654, scalar12654, tp12654, tm12654, ep12654, em12654, dsL]

theorem negative12654 :
    Eminus aL (agent12654.root+dsL) scalar12654.worldRadius world12654.frame
      agent12654.frame tm12654 ≤ -em12654 := by
  apply negative_check (lo := (34223947459202634347 / 50000000000000000000)) (hi := (13689578983681053739 / 20000000000000000000))
    (y := (-((35846618552594900129 / 50000000000000000000)))) (u := (24412386193424639519 / 50000000000000000000))
  · norm_num [world12654, agent12654, scalar12654, tp12654, tm12654, ep12654, em12654, dsL]
  · norm_num [world12654, agent12654, scalar12654, tp12654, tm12654, ep12654, em12654, dsL]
  · norm_num [world12654, agent12654, scalar12654, tp12654, tm12654, ep12654, em12654, dsL]
  · norm_num [world12654, agent12654, scalar12654, tp12654, tm12654, ep12654, em12654, dsL]
  · norm_num [world12654, agent12654, scalar12654, tp12654, tm12654, ep12654, em12654, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12654, agent12654, tp12654, tm12654, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12654, agent12654, tp12654, tm12654, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12654, agent12654, scalar12654, tp12654, tm12654, ep12654, em12654, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12654, agent12654, tp12654, tm12654, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12654, agent12654, scalar12654, tp12654, tm12654, ep12654, em12654, dsL]

theorem tails12654 :
    exp (-((12654:ℝ)*ep12654)) ≤ scalar12654.upperTail ∧
    exp (-((12654:ℝ)*em12654)) ≤ scalar12654.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12654:ℝ)) (by norm_num [ep12654]) ?_)
      (show bp12654^8 ≤ scalar12654.upperTail by norm_num [bp12654, scalar12654])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12654, bp12654, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12654:ℝ)) (by norm_num [em12654]) ?_)
      (show bm12654^8 ≤ scalar12654.lowerTail by norm_num [bm12654, scalar12654])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12654, bm12654, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12654 :
    agent12654.root+dsL+scalar12654.worldRadius < √(1/100/aL) ∧
    2*(agent12654.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12654, agent12654, scalar12654, tp12654, tm12654, ep12654, em12654, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12654, agent12654, scalar12654, tp12654, tm12654, ep12654, em12654, dsL]

noncomputable def master12654 : MasterCertificate 12654 world12654 agent12654 :=
  master scalar12654 dsL tp12654 tm12654 ep12654 em12654
    (by norm_num [dsL]) (by norm_num [tp12654]) (by norm_num [tm12654])
    (by norm_num [ep12654]) (by norm_num [em12654])
    positive12654 negative12654 tails12654.1 tails12654.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12654.1 tailGuards12654.2

theorem preserves12654 : master12654.toScalarCertificate = scalar12654 := rfl

noncomputable def tp12655 : ℝ := (1156126003 / 5000000000)
noncomputable def tm12655 : ℝ := (-((6053484827 / 10000000000)))
noncomputable def ep12655 : ℝ := (12824635359562927 / 25000000000000000000)
noncomputable def em12655 : ℝ := (49999758631736951 / 100000000000000000000)
noncomputable def bp12655 : ℝ := (5552508690476999661 / 12500000000000000000)
noncomputable def bm12655 : ℝ := (45342124639238274369 / 100000000000000000000)

theorem positive12655 :
    Eplus aL (agent12655.root+dsL) scalar12655.worldRadius world12655.frame
      agent12655.frame tp12655 ≤ -ep12655 := by
  apply positive_check (eT := (115581442392488969469 / 100000000000000000000)) (y := (7565753643178293401 / 20000000000000000000)) (u := (145978283595282076447 / 100000000000000000000))
  · norm_num [world12655, agent12655, scalar12655, tp12655, tm12655, ep12655, em12655, dsL]
  · norm_num [world12655, agent12655, scalar12655, tp12655, tm12655, ep12655, em12655, dsL]
  · norm_num [world12655, agent12655, scalar12655, tp12655, tm12655, ep12655, em12655, dsL]
  · norm_num [world12655, agent12655, scalar12655, tp12655, tm12655, ep12655, em12655, dsL]
  · norm_num [world12655, agent12655, scalar12655, tp12655, tm12655, ep12655, em12655, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12655, agent12655, tp12655, tm12655, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12655, agent12655, scalar12655, tp12655, tm12655, ep12655, em12655, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12655, agent12655, tp12655, tm12655, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12655, agent12655, scalar12655, tp12655, tm12655, ep12655, em12655, dsL]

theorem negative12655 :
    Eminus aL (agent12655.root+dsL) scalar12655.worldRadius world12655.frame
      agent12655.frame tm12655 ≤ -em12655 := by
  apply negative_check (lo := (34223835971529112627 / 50000000000000000000)) (hi := (13689534388611645051 / 20000000000000000000))
    (y := (-((71693329330321133029 / 100000000000000000000)))) (u := (48824727358159586227 / 100000000000000000000))
  · norm_num [world12655, agent12655, scalar12655, tp12655, tm12655, ep12655, em12655, dsL]
  · norm_num [world12655, agent12655, scalar12655, tp12655, tm12655, ep12655, em12655, dsL]
  · norm_num [world12655, agent12655, scalar12655, tp12655, tm12655, ep12655, em12655, dsL]
  · norm_num [world12655, agent12655, scalar12655, tp12655, tm12655, ep12655, em12655, dsL]
  · norm_num [world12655, agent12655, scalar12655, tp12655, tm12655, ep12655, em12655, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12655, agent12655, tp12655, tm12655, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12655, agent12655, tp12655, tm12655, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12655, agent12655, scalar12655, tp12655, tm12655, ep12655, em12655, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12655, agent12655, tp12655, tm12655, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12655, agent12655, scalar12655, tp12655, tm12655, ep12655, em12655, dsL]

theorem tails12655 :
    exp (-((12655:ℝ)*ep12655)) ≤ scalar12655.upperTail ∧
    exp (-((12655:ℝ)*em12655)) ≤ scalar12655.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12655:ℝ)) (by norm_num [ep12655]) ?_)
      (show bp12655^8 ≤ scalar12655.upperTail by norm_num [bp12655, scalar12655])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12655, bp12655, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12655:ℝ)) (by norm_num [em12655]) ?_)
      (show bm12655^8 ≤ scalar12655.lowerTail by norm_num [bm12655, scalar12655])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12655, bm12655, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12655 :
    agent12655.root+dsL+scalar12655.worldRadius < √(1/100/aL) ∧
    2*(agent12655.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12655, agent12655, scalar12655, tp12655, tm12655, ep12655, em12655, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12655, agent12655, scalar12655, tp12655, tm12655, ep12655, em12655, dsL]

noncomputable def master12655 : MasterCertificate 12655 world12655 agent12655 :=
  master scalar12655 dsL tp12655 tm12655 ep12655 em12655
    (by norm_num [dsL]) (by norm_num [tp12655]) (by norm_num [tm12655])
    (by norm_num [ep12655]) (by norm_num [em12655])
    positive12655 negative12655 tails12655.1 tails12655.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12655.1 tailGuards12655.2

theorem preserves12655 : master12655.toScalarCertificate = scalar12655 := rfl

noncomputable def tp12656 : ℝ := (578084723 / 2500000000)
noncomputable def tm12656 : ℝ := (-((6053671593 / 10000000000)))
noncomputable def ep12656 : ℝ := (1282530497004527 / 2500000000000000000)
noncomputable def em12656 : ℝ := (12500514867982129 / 25000000000000000000)
noncomputable def bp12656 : ℝ := (2775958700642836061 / 6250000000000000000)
noncomputable def bm12656 : ℝ := (5667205071330016377 / 12500000000000000000)

theorem positive12656 :
    Eplus aL (agent12656.root+dsL) scalar12656.worldRadius world12656.frame
      agent12656.frame tp12656 ≤ -ep12656 := by
  apply positive_check (eT := (57790849331623928091 / 50000000000000000000)) (y := (37829579798390943267 / 100000000000000000000)) (u := (36494867083573083079 / 25000000000000000000))
  · norm_num [world12656, agent12656, scalar12656, tp12656, tm12656, ep12656, em12656, dsL]
  · norm_num [world12656, agent12656, scalar12656, tp12656, tm12656, ep12656, em12656, dsL]
  · norm_num [world12656, agent12656, scalar12656, tp12656, tm12656, ep12656, em12656, dsL]
  · norm_num [world12656, agent12656, scalar12656, tp12656, tm12656, ep12656, em12656, dsL]
  · norm_num [world12656, agent12656, scalar12656, tp12656, tm12656, ep12656, em12656, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12656, agent12656, tp12656, tm12656, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12656, agent12656, scalar12656, tp12656, tm12656, ep12656, em12656, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12656, agent12656, tp12656, tm12656, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12656, agent12656, scalar12656, tp12656, tm12656, ep12656, em12656, dsL]

theorem negative12656 :
    Eminus aL (agent12656.root+dsL) scalar12656.worldRadius world12656.frame
      agent12656.frame tm12656 ≤ -em12656 := by
  apply negative_check (lo := (13689489818212916783 / 20000000000000000000)) (hi := (17111862272766145979 / 25000000000000000000))
    (y := (-((8961677715124650121 / 12500000000000000000)))) (u := (48824682248684730173 / 100000000000000000000))
  · norm_num [world12656, agent12656, scalar12656, tp12656, tm12656, ep12656, em12656, dsL]
  · norm_num [world12656, agent12656, scalar12656, tp12656, tm12656, ep12656, em12656, dsL]
  · norm_num [world12656, agent12656, scalar12656, tp12656, tm12656, ep12656, em12656, dsL]
  · norm_num [world12656, agent12656, scalar12656, tp12656, tm12656, ep12656, em12656, dsL]
  · norm_num [world12656, agent12656, scalar12656, tp12656, tm12656, ep12656, em12656, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12656, agent12656, tp12656, tm12656, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12656, agent12656, tp12656, tm12656, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12656, agent12656, scalar12656, tp12656, tm12656, ep12656, em12656, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12656, agent12656, tp12656, tm12656, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12656, agent12656, scalar12656, tp12656, tm12656, ep12656, em12656, dsL]

theorem tails12656 :
    exp (-((12656:ℝ)*ep12656)) ≤ scalar12656.upperTail ∧
    exp (-((12656:ℝ)*em12656)) ≤ scalar12656.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12656:ℝ)) (by norm_num [ep12656]) ?_)
      (show bp12656^8 ≤ scalar12656.upperTail by norm_num [bp12656, scalar12656])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12656, bp12656, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12656:ℝ)) (by norm_num [em12656]) ?_)
      (show bm12656^8 ≤ scalar12656.lowerTail by norm_num [bm12656, scalar12656])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12656, bm12656, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12656 :
    agent12656.root+dsL+scalar12656.worldRadius < √(1/100/aL) ∧
    2*(agent12656.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12656, agent12656, scalar12656, tp12656, tm12656, ep12656, em12656, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12656, agent12656, scalar12656, tp12656, tm12656, ep12656, em12656, dsL]

noncomputable def master12656 : MasterCertificate 12656 world12656 agent12656 :=
  master scalar12656 dsL tp12656 tm12656 ep12656 em12656
    (by norm_num [dsL]) (by norm_num [tp12656]) (by norm_num [tm12656])
    (by norm_num [ep12656]) (by norm_num [em12656])
    positive12656 negative12656 tails12656.1 tails12656.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12656.1 tailGuards12656.2

theorem preserves12656 : master12656.toScalarCertificate = scalar12656 := rfl

noncomputable def tp12657 : ℝ := (462485153 / 2000000000)
noncomputable def tm12657 : ℝ := (-((756732269 / 1250000000)))
noncomputable def ep12657 : ℝ := (51303896260720009 / 100000000000000000000)
noncomputable def em12657 : ℝ := (50004358373932977 / 100000000000000000000)
noncomputable def bp12657 : ℝ := (22205305275753743157 / 50000000000000000000)
noncomputable def bm12657 : ℝ := (45333158074849583051 / 100000000000000000000)

theorem positive12657 :
    Eplus aL (agent12657.root+dsL) scalar12657.worldRadius world12657.frame
      agent12657.frame tp12657 ≤ -ep12657 := by
  apply positive_check (eT := (23116390974512054447 / 20000000000000000000)) (y := (37830391728643750547 / 100000000000000000000)) (u := (29196130718114069259 / 20000000000000000000))
  · norm_num [world12657, agent12657, scalar12657, tp12657, tm12657, ep12657, em12657, dsL]
  · norm_num [world12657, agent12657, scalar12657, tp12657, tm12657, ep12657, em12657, dsL]
  · norm_num [world12657, agent12657, scalar12657, tp12657, tm12657, ep12657, em12657, dsL]
  · norm_num [world12657, agent12657, scalar12657, tp12657, tm12657, ep12657, em12657, dsL]
  · norm_num [world12657, agent12657, scalar12657, tp12657, tm12657, ep12657, em12657, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12657, agent12657, tp12657, tm12657, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12657, agent12657, scalar12657, tp12657, tm12657, ep12657, em12657, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12657, agent12657, tp12657, tm12657, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12657, agent12657, scalar12657, tp12657, tm12657, ep12657, em12657, dsL]

theorem negative12657 :
    Eminus aL (agent12657.root+dsL) scalar12657.worldRadius world12657.frame
      agent12657.frame tm12657 ≤ -em12657 := by
  apply negative_check (lo := (68447227069564052807 / 100000000000000000000)) (hi := (8555903383695506601 / 12500000000000000000))
    (y := (-((35846756353603376173 / 50000000000000000000)))) (u := (24412318912488618159 / 50000000000000000000))
  · norm_num [world12657, agent12657, scalar12657, tp12657, tm12657, ep12657, em12657, dsL]
  · norm_num [world12657, agent12657, scalar12657, tp12657, tm12657, ep12657, em12657, dsL]
  · norm_num [world12657, agent12657, scalar12657, tp12657, tm12657, ep12657, em12657, dsL]
  · norm_num [world12657, agent12657, scalar12657, tp12657, tm12657, ep12657, em12657, dsL]
  · norm_num [world12657, agent12657, scalar12657, tp12657, tm12657, ep12657, em12657, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12657, agent12657, tp12657, tm12657, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12657, agent12657, tp12657, tm12657, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12657, agent12657, scalar12657, tp12657, tm12657, ep12657, em12657, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12657, agent12657, tp12657, tm12657, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12657, agent12657, scalar12657, tp12657, tm12657, ep12657, em12657, dsL]

theorem tails12657 :
    exp (-((12657:ℝ)*ep12657)) ≤ scalar12657.upperTail ∧
    exp (-((12657:ℝ)*em12657)) ≤ scalar12657.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12657:ℝ)) (by norm_num [ep12657]) ?_)
      (show bp12657^8 ≤ scalar12657.upperTail by norm_num [bp12657, scalar12657])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12657, bp12657, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12657:ℝ)) (by norm_num [em12657]) ?_)
      (show bm12657^8 ≤ scalar12657.lowerTail by norm_num [bm12657, scalar12657])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12657, bm12657, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12657 :
    agent12657.root+dsL+scalar12657.worldRadius < √(1/100/aL) ∧
    2*(agent12657.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12657, agent12657, scalar12657, tp12657, tm12657, ep12657, em12657, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12657, agent12657, scalar12657, tp12657, tm12657, ep12657, em12657, dsL]

noncomputable def master12657 : MasterCertificate 12657 world12657 agent12657 :=
  master scalar12657 dsL tp12657 tm12657 ep12657 em12657
    (by norm_num [dsL]) (by norm_num [tp12657]) (by norm_num [tm12657])
    (by norm_num [ep12657]) (by norm_num [em12657])
    positive12657 negative12657 tails12657.1 tails12657.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12657.1 tailGuards12657.2

theorem preserves12657 : master12657.toScalarCertificate = scalar12657 := rfl

noncomputable def tp12658 : ℝ := (115625629 / 500000000)
noncomputable def tm12658 : ℝ := (-((5912153 / 9765625)))
noncomputable def ep12658 : ℝ := (51306572297816913 / 100000000000000000000)
noncomputable def em12658 : ℝ := (390677007551451 / 781250000000000000)
noncomputable def bp12658 : ℝ := (4440588234035300497 / 10000000000000000000)
noncomputable def bm12658 : ℝ := (45328675983595362439 / 100000000000000000000)

theorem positive12658 :
    Eplus aL (agent12658.root+dsL) scalar12658.worldRadius world12658.frame
      agent12658.frame tp12658 ≤ -ep12658 := by
  apply positive_check (eT := (115582210694654315133 / 100000000000000000000)) (y := (37831202867406928983 / 100000000000000000000)) (u := (9123864856315046479 / 6250000000000000000))
  · norm_num [world12658, agent12658, scalar12658, tp12658, tm12658, ep12658, em12658, dsL]
  · norm_num [world12658, agent12658, scalar12658, tp12658, tm12658, ep12658, em12658, dsL]
  · norm_num [world12658, agent12658, scalar12658, tp12658, tm12658, ep12658, em12658, dsL]
  · norm_num [world12658, agent12658, scalar12658, tp12658, tm12658, ep12658, em12658, dsL]
  · norm_num [world12658, agent12658, scalar12658, tp12658, tm12658, ep12658, em12658, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12658, agent12658, tp12658, tm12658, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12658, agent12658, scalar12658, tp12658, tm12658, ep12658, em12658, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12658, agent12658, tp12658, tm12658, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12658, agent12658, scalar12658, tp12658, tm12658, ep12658, em12658, dsL]

theorem negative12658 :
    Eminus aL (agent12658.root+dsL) scalar12658.worldRadius world12658.frame
      agent12658.frame tm12658 ≤ -em12658 := by
  apply negative_check (lo := (6844700515851994791 / 10000000000000000000)) (hi := (68447005158519947911 / 100000000000000000000))
    (y := (-((17923401036763148169 / 25000000000000000000)))) (u := (6103074147478011099 / 12500000000000000000))
  · norm_num [world12658, agent12658, scalar12658, tp12658, tm12658, ep12658, em12658, dsL]
  · norm_num [world12658, agent12658, scalar12658, tp12658, tm12658, ep12658, em12658, dsL]
  · norm_num [world12658, agent12658, scalar12658, tp12658, tm12658, ep12658, em12658, dsL]
  · norm_num [world12658, agent12658, scalar12658, tp12658, tm12658, ep12658, em12658, dsL]
  · norm_num [world12658, agent12658, scalar12658, tp12658, tm12658, ep12658, em12658, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12658, agent12658, tp12658, tm12658, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12658, agent12658, tp12658, tm12658, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12658, agent12658, scalar12658, tp12658, tm12658, ep12658, em12658, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12658, agent12658, tp12658, tm12658, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12658, agent12658, scalar12658, tp12658, tm12658, ep12658, em12658, dsL]

theorem tails12658 :
    exp (-((12658:ℝ)*ep12658)) ≤ scalar12658.upperTail ∧
    exp (-((12658:ℝ)*em12658)) ≤ scalar12658.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12658:ℝ)) (by norm_num [ep12658]) ?_)
      (show bp12658^8 ≤ scalar12658.upperTail by norm_num [bp12658, scalar12658])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12658, bp12658, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12658:ℝ)) (by norm_num [em12658]) ?_)
      (show bm12658^8 ≤ scalar12658.lowerTail by norm_num [bm12658, scalar12658])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12658, bm12658, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12658 :
    agent12658.root+dsL+scalar12658.worldRadius < √(1/100/aL) ∧
    2*(agent12658.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12658, agent12658, scalar12658, tp12658, tm12658, ep12658, em12658, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12658, agent12658, scalar12658, tp12658, tm12658, ep12658, em12658, dsL]

noncomputable def master12658 : MasterCertificate 12658 world12658 agent12658 :=
  master scalar12658 dsL tp12658 tm12658 ep12658 em12658
    (by norm_num [dsL]) (by norm_num [tp12658]) (by norm_num [tm12658])
    (by norm_num [ep12658]) (by norm_num [em12658])
    positive12658 negative12658 tails12658.1 tails12658.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12658.1 tailGuards12658.2

theorem preserves12658 : master12658.toScalarCertificate = scalar12658 := rfl

noncomputable def tp12659 : ℝ := (2312599383 / 10000000000)
noncomputable def tm12659 : ℝ := (-((6054231009 / 10000000000)))
noncomputable def ep12659 : ℝ := (25654623221003477 / 50000000000000000000)
noncomputable def em12659 : ℝ := (10001790759787103 / 20000000000000000000)
noncomputable def bp12659 : ℝ := (44401155665486151003 / 100000000000000000000)
noncomputable def bm12659 : ℝ := (11331048834379521787 / 25000000000000000000)

theorem positive12659 :
    Eplus aL (agent12659.root+dsL) scalar12659.worldRadius world12659.frame
      agent12659.frame tp12659 ≤ -ep12659 := by
  apply positive_check (eT := (23116493292499552661 / 20000000000000000000)) (y := (1891600716066387077 / 5000000000000000000)) (u := (145983022281192597527 / 100000000000000000000))
  · norm_num [world12659, agent12659, scalar12659, tp12659, tm12659, ep12659, em12659, dsL]
  · norm_num [world12659, agent12659, scalar12659, tp12659, tm12659, ep12659, em12659, dsL]
  · norm_num [world12659, agent12659, scalar12659, tp12659, tm12659, ep12659, em12659, dsL]
  · norm_num [world12659, agent12659, scalar12659, tp12659, tm12659, ep12659, em12659, dsL]
  · norm_num [world12659, agent12659, scalar12659, tp12659, tm12659, ep12659, em12659, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12659, agent12659, tp12659, tm12659, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12659, agent12659, scalar12659, tp12659, tm12659, ep12659, em12659, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12659, agent12659, tp12659, tm12659, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12659, agent12659, scalar12659, tp12659, tm12659, ep12659, em12659, dsL]

theorem negative12659 :
    Eminus aL (agent12659.root+dsL) scalar12659.worldRadius world12659.frame
      agent12659.frame tm12659 ≤ -em12659 := by
  apply negative_check (lo := (34223391987555732187 / 50000000000000000000)) (hi := (109514854360178343 / 160000000000000000))
    (y := (-((14338738908153450949 / 20000000000000000000)))) (u := (9764909809096118449 / 20000000000000000000))
  · norm_num [world12659, agent12659, scalar12659, tp12659, tm12659, ep12659, em12659, dsL]
  · norm_num [world12659, agent12659, scalar12659, tp12659, tm12659, ep12659, em12659, dsL]
  · norm_num [world12659, agent12659, scalar12659, tp12659, tm12659, ep12659, em12659, dsL]
  · norm_num [world12659, agent12659, scalar12659, tp12659, tm12659, ep12659, em12659, dsL]
  · norm_num [world12659, agent12659, scalar12659, tp12659, tm12659, ep12659, em12659, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12659, agent12659, tp12659, tm12659, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12659, agent12659, tp12659, tm12659, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12659, agent12659, scalar12659, tp12659, tm12659, ep12659, em12659, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12659, agent12659, tp12659, tm12659, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12659, agent12659, scalar12659, tp12659, tm12659, ep12659, em12659, dsL]

theorem tails12659 :
    exp (-((12659:ℝ)*ep12659)) ≤ scalar12659.upperTail ∧
    exp (-((12659:ℝ)*em12659)) ≤ scalar12659.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12659:ℝ)) (by norm_num [ep12659]) ?_)
      (show bp12659^8 ≤ scalar12659.upperTail by norm_num [bp12659, scalar12659])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12659, bp12659, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12659:ℝ)) (by norm_num [em12659]) ?_)
      (show bm12659^8 ≤ scalar12659.lowerTail by norm_num [bm12659, scalar12659])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12659, bm12659, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12659 :
    agent12659.root+dsL+scalar12659.worldRadius < √(1/100/aL) ∧
    2*(agent12659.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12659, agent12659, scalar12659, tp12659, tm12659, ep12659, em12659, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12659, agent12659, scalar12659, tp12659, tm12659, ep12659, em12659, dsL]

noncomputable def master12659 : MasterCertificate 12659 world12659 agent12659 :=
  master scalar12659 dsL tp12659 tm12659 ep12659 em12659
    (by norm_num [dsL]) (by norm_num [tp12659]) (by norm_num [tm12659])
    (by norm_num [ep12659]) (by norm_num [em12659])
    positive12659 negative12659 tails12659.1 tails12659.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12659.1 tailGuards12659.2

theorem preserves12659 : master12659.toScalarCertificate = scalar12659 := rfl

noncomputable def tp12660 : ℝ := (2312760813 / 10000000000)
noncomputable def tm12660 : ℝ := (-((3027321669 / 5000000000)))
noncomputable def ep12660 : ℝ := (25656674633356549 / 50000000000000000000)
noncomputable def em12660 : ℝ := (2000512271573971 / 4000000000000000000)
noncomputable def bp12660 : ℝ := (22197712727610001273 / 50000000000000000000)
noncomputable def bm12660 : ℝ := (11329649708857934761 / 25000000000000000000)

theorem positive12660 :
    Eplus aL (agent12660.root+dsL) scalar12660.worldRadius world12660.frame
      agent12660.frame tp12660 ≤ -ep12660 := by
  apply positive_check (eT := (28895815595860361839 / 25000000000000000000)) (y := (37832097760807432427 / 100000000000000000000)) (u := (145983144088717643761 / 100000000000000000000))
  · norm_num [world12660, agent12660, scalar12660, tp12660, tm12660, ep12660, em12660, dsL]
  · norm_num [world12660, agent12660, scalar12660, tp12660, tm12660, ep12660, em12660, dsL]
  · norm_num [world12660, agent12660, scalar12660, tp12660, tm12660, ep12660, em12660, dsL]
  · norm_num [world12660, agent12660, scalar12660, tp12660, tm12660, ep12660, em12660, dsL]
  · norm_num [world12660, agent12660, scalar12660, tp12660, tm12660, ep12660, em12660, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12660, agent12660, tp12660, tm12660, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12660, agent12660, scalar12660, tp12660, tm12660, ep12660, em12660, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12660, agent12660, tp12660, tm12660, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12660, agent12660, scalar12660, tp12660, tm12660, ep12660, em12660, dsL]

theorem negative12660 :
    Eminus aL (agent12660.root+dsL) scalar12660.worldRadius world12660.frame
      agent12660.frame tm12660 ≤ -em12660 := by
  apply negative_check (lo := (34222797069801730431 / 50000000000000000000)) (hi := (68445594139603460863 / 100000000000000000000))
    (y := (-((4480742133042080029 / 6250000000000000000)))) (u := (48825437861566277791 / 100000000000000000000))
  · norm_num [world12660, agent12660, scalar12660, tp12660, tm12660, ep12660, em12660, dsL]
  · norm_num [world12660, agent12660, scalar12660, tp12660, tm12660, ep12660, em12660, dsL]
  · norm_num [world12660, agent12660, scalar12660, tp12660, tm12660, ep12660, em12660, dsL]
  · norm_num [world12660, agent12660, scalar12660, tp12660, tm12660, ep12660, em12660, dsL]
  · norm_num [world12660, agent12660, scalar12660, tp12660, tm12660, ep12660, em12660, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12660, agent12660, tp12660, tm12660, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12660, agent12660, tp12660, tm12660, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12660, agent12660, scalar12660, tp12660, tm12660, ep12660, em12660, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12660, agent12660, tp12660, tm12660, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12660, agent12660, scalar12660, tp12660, tm12660, ep12660, em12660, dsL]

theorem tails12660 :
    exp (-((12660:ℝ)*ep12660)) ≤ scalar12660.upperTail ∧
    exp (-((12660:ℝ)*em12660)) ≤ scalar12660.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12660:ℝ)) (by norm_num [ep12660]) ?_)
      (show bp12660^8 ≤ scalar12660.upperTail by norm_num [bp12660, scalar12660])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12660, bp12660, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12660:ℝ)) (by norm_num [em12660]) ?_)
      (show bm12660^8 ≤ scalar12660.lowerTail by norm_num [bm12660, scalar12660])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12660, bm12660, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12660 :
    agent12660.root+dsL+scalar12660.worldRadius < √(1/100/aL) ∧
    2*(agent12660.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12660, agent12660, scalar12660, tp12660, tm12660, ep12660, em12660, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12660, agent12660, scalar12660, tp12660, tm12660, ep12660, em12660, dsL]

noncomputable def master12660 : MasterCertificate 12660 world12660 agent12660 :=
  master scalar12660 dsL tp12660 tm12660 ep12660 em12660
    (by norm_num [dsL]) (by norm_num [tp12660]) (by norm_num [tm12660])
    (by norm_num [ep12660]) (by norm_num [em12660])
    positive12660 negative12660 tails12660.1 tails12660.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12660.1 tailGuards12660.2

theorem preserves12660 : master12660.toScalarCertificate = scalar12660 := rfl

noncomputable def tp12661 : ℝ := (57821189 / 250000000)
noncomputable def tm12661 : ℝ := (-((6054829537 / 10000000000)))
noncomputable def ep12661 : ℝ := (51316020801123259 / 100000000000000000000)
noncomputable def em12661 : ℝ := (6251887651444611 / 12500000000000000000)
noncomputable def bp12661 : ℝ := (44390701054070104481 / 100000000000000000000)
noncomputable def bm12661 : ℝ := (45314120305359863643 / 100000000000000000000)

theorem positive12661 :
    Eplus aL (agent12661.root+dsL) scalar12661.worldRadius world12661.frame
      agent12661.frame tp12661 ≤ -ep12661 := by
  apply positive_check (eT := (57791758900185282961 / 50000000000000000000)) (y := (18916454473998587691 / 50000000000000000000)) (u := (1824804103626058923 / 1250000000000000000))
  · norm_num [world12661, agent12661, scalar12661, tp12661, tm12661, ep12661, em12661, dsL]
  · norm_num [world12661, agent12661, scalar12661, tp12661, tm12661, ep12661, em12661, dsL]
  · norm_num [world12661, agent12661, scalar12661, tp12661, tm12661, ep12661, em12661, dsL]
  · norm_num [world12661, agent12661, scalar12661, tp12661, tm12661, ep12661, em12661, dsL]
  · norm_num [world12661, agent12661, scalar12661, tp12661, tm12661, ep12661, em12661, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12661, agent12661, tp12661, tm12661, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12661, agent12661, scalar12661, tp12661, tm12661, ep12661, em12661, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12661, agent12661, tp12661, tm12661, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12661, agent12661, scalar12661, tp12661, tm12661, ep12661, em12661, dsL]

theorem negative12661 :
    Eminus aL (agent12661.root+dsL) scalar12661.worldRadius world12661.frame
      agent12661.frame tm12661 ≤ -em12661 := by
  apply negative_check (lo := (17111343364703158853 / 25000000000000000000)) (hi := (68445373458812635413 / 100000000000000000000))
    (y := (-((2867678580187556487 / 4000000000000000000)))) (u := (12206348433775215911 / 25000000000000000000))
  · norm_num [world12661, agent12661, scalar12661, tp12661, tm12661, ep12661, em12661, dsL]
  · norm_num [world12661, agent12661, scalar12661, tp12661, tm12661, ep12661, em12661, dsL]
  · norm_num [world12661, agent12661, scalar12661, tp12661, tm12661, ep12661, em12661, dsL]
  · norm_num [world12661, agent12661, scalar12661, tp12661, tm12661, ep12661, em12661, dsL]
  · norm_num [world12661, agent12661, scalar12661, tp12661, tm12661, ep12661, em12661, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12661, agent12661, tp12661, tm12661, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12661, agent12661, tp12661, tm12661, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12661, agent12661, scalar12661, tp12661, tm12661, ep12661, em12661, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12661, agent12661, tp12661, tm12661, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12661, agent12661, scalar12661, tp12661, tm12661, ep12661, em12661, dsL]

theorem tails12661 :
    exp (-((12661:ℝ)*ep12661)) ≤ scalar12661.upperTail ∧
    exp (-((12661:ℝ)*em12661)) ≤ scalar12661.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12661:ℝ)) (by norm_num [ep12661]) ?_)
      (show bp12661^8 ≤ scalar12661.upperTail by norm_num [bp12661, scalar12661])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12661, bp12661, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12661:ℝ)) (by norm_num [em12661]) ?_)
      (show bm12661^8 ≤ scalar12661.lowerTail by norm_num [bm12661, scalar12661])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12661, bm12661, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12661 :
    agent12661.root+dsL+scalar12661.worldRadius < √(1/100/aL) ∧
    2*(agent12661.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12661, agent12661, scalar12661, tp12661, tm12661, ep12661, em12661, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12661, agent12661, scalar12661, tp12661, tm12661, ep12661, em12661, dsL]

noncomputable def master12661 : MasterCertificate 12661 world12661 agent12661 :=
  master scalar12661 dsL tp12661 tm12661 ep12661 em12661
    (by norm_num [dsL]) (by norm_num [tp12661]) (by norm_num [tm12661])
    (by norm_num [ep12661]) (by norm_num [em12661])
    positive12661 negative12661 tails12661.1 tails12661.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12661.1 tailGuards12661.2

theorem preserves12661 : master12661.toScalarCertificate = scalar12661 := rfl

noncomputable def tp12662 : ℝ := (1156467123 / 5000000000)
noncomputable def tm12662 : ℝ := (-((3027507867 / 5000000000)))
noncomputable def ep12662 : ℝ := (3207418211235421 / 6250000000000000000)
noncomputable def em12662 : ℝ := (15630435856579 / 31250000000000000)
noncomputable def bp12662 : ℝ := (22192988765335795883 / 50000000000000000000)
noncomputable def bm12662 : ℝ := (45309642598169956933 / 100000000000000000000)

theorem positive12662 :
    Eplus aL (agent12662.root+dsL) scalar12662.worldRadius world12662.frame
      agent12662.frame tp12662 ≤ -ep12662 := by
  apply positive_check (eT := (57791886404207007617 / 50000000000000000000)) (y := (591151867046649653 / 1562500000000000000)) (u := (145985511560617287167 / 100000000000000000000))
  · norm_num [world12662, agent12662, scalar12662, tp12662, tm12662, ep12662, em12662, dsL]
  · norm_num [world12662, agent12662, scalar12662, tp12662, tm12662, ep12662, em12662, dsL]
  · norm_num [world12662, agent12662, scalar12662, tp12662, tm12662, ep12662, em12662, dsL]
  · norm_num [world12662, agent12662, scalar12662, tp12662, tm12662, ep12662, em12662, dsL]
  · norm_num [world12662, agent12662, scalar12662, tp12662, tm12662, ep12662, em12662, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12662, agent12662, tp12662, tm12662, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12662, agent12662, scalar12662, tp12662, tm12662, ep12662, em12662, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12662, agent12662, tp12662, tm12662, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12662, agent12662, scalar12662, tp12662, tm12662, ep12662, em12662, dsL]

theorem negative12662 :
    Eminus aL (agent12662.root+dsL) scalar12662.worldRadius world12662.frame
      agent12662.frame tm12662 ≤ -em12662 := by
  apply negative_check (lo := (17111288182464091049 / 25000000000000000000)) (hi := (68445152729856364197 / 100000000000000000000))
    (y := (-((71692055852518898301 / 100000000000000000000)))) (u := (12206337283545893859 / 25000000000000000000))
  · norm_num [world12662, agent12662, scalar12662, tp12662, tm12662, ep12662, em12662, dsL]
  · norm_num [world12662, agent12662, scalar12662, tp12662, tm12662, ep12662, em12662, dsL]
  · norm_num [world12662, agent12662, scalar12662, tp12662, tm12662, ep12662, em12662, dsL]
  · norm_num [world12662, agent12662, scalar12662, tp12662, tm12662, ep12662, em12662, dsL]
  · norm_num [world12662, agent12662, scalar12662, tp12662, tm12662, ep12662, em12662, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12662, agent12662, tp12662, tm12662, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12662, agent12662, tp12662, tm12662, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12662, agent12662, scalar12662, tp12662, tm12662, ep12662, em12662, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12662, agent12662, tp12662, tm12662, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12662, agent12662, scalar12662, tp12662, tm12662, ep12662, em12662, dsL]

theorem tails12662 :
    exp (-((12662:ℝ)*ep12662)) ≤ scalar12662.upperTail ∧
    exp (-((12662:ℝ)*em12662)) ≤ scalar12662.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12662:ℝ)) (by norm_num [ep12662]) ?_)
      (show bp12662^8 ≤ scalar12662.upperTail by norm_num [bp12662, scalar12662])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12662, bp12662, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12662:ℝ)) (by norm_num [em12662]) ?_)
      (show bm12662^8 ≤ scalar12662.lowerTail by norm_num [bm12662, scalar12662])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12662, bm12662, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12662 :
    agent12662.root+dsL+scalar12662.worldRadius < √(1/100/aL) ∧
    2*(agent12662.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12662, agent12662, scalar12662, tp12662, tm12662, ep12662, em12662, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12662, agent12662, scalar12662, tp12662, tm12662, ep12662, em12662, dsL]

noncomputable def master12662 : MasterCertificate 12662 world12662 agent12662 :=
  master scalar12662 dsL tp12662 tm12662 ep12662 em12662
    (by norm_num [dsL]) (by norm_num [tp12662]) (by norm_num [tm12662])
    (by norm_num [ep12662]) (by norm_num [em12662])
    positive12662 negative12662 tails12662.1 tails12662.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12662.1 tailGuards12662.2

theorem preserves12662 : master12662.toScalarCertificate = scalar12662 := rfl

noncomputable def tp12663 : ℝ := (462604163 / 2000000000)
noncomputable def tm12663 : ℝ := (-((6055201617 / 10000000000)))
noncomputable def ep12663 : ℝ := (51321359123654757 / 100000000000000000000)
noncomputable def em12663 : ℝ := (50019685638918317 / 100000000000000000000)
noncomputable def bp12663 : ℝ := (44381256204999557043 / 100000000000000000000)
noncomputable def bm12663 : ℝ := (11326291740219450949 / 25000000000000000000)

theorem positive12663 :
    Eplus aL (agent12663.root+dsL) scalar12663.worldRadius world12663.frame
      agent12663.frame tp12663 ≤ -ep12663 := by
  apply positive_check (eT := (11558402700234976099 / 10000000000000000000)) (y := (37834528601379437229 / 100000000000000000000)) (u := (36496673187335851731 / 25000000000000000000))
  · norm_num [world12663, agent12663, scalar12663, tp12663, tm12663, ep12663, em12663, dsL]
  · norm_num [world12663, agent12663, scalar12663, tp12663, tm12663, ep12663, em12663, dsL]
  · norm_num [world12663, agent12663, scalar12663, tp12663, tm12663, ep12663, em12663, dsL]
  · norm_num [world12663, agent12663, scalar12663, tp12663, tm12663, ep12663, em12663, dsL]
  · norm_num [world12663, agent12663, scalar12663, tp12663, tm12663, ep12663, em12663, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12663, agent12663, tp12663, tm12663, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12663, agent12663, scalar12663, tp12663, tm12663, ep12663, em12663, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12663, agent12663, tp12663, tm12663, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12663, agent12663, scalar12663, tp12663, tm12663, ep12663, em12663, dsL]

theorem negative12663 :
    Eminus aL (agent12663.root+dsL) scalar12663.worldRadius world12663.frame
      agent12663.frame tm12663 ≤ -em12663 := by
  apply negative_check (lo := (68444933289796090303 / 100000000000000000000)) (hi := (1069452082653063911 / 1562500000000000000))
    (y := (-((71692144621118182291 / 100000000000000000000)))) (u := (24412652896312145177 / 50000000000000000000))
  · norm_num [world12663, agent12663, scalar12663, tp12663, tm12663, ep12663, em12663, dsL]
  · norm_num [world12663, agent12663, scalar12663, tp12663, tm12663, ep12663, em12663, dsL]
  · norm_num [world12663, agent12663, scalar12663, tp12663, tm12663, ep12663, em12663, dsL]
  · norm_num [world12663, agent12663, scalar12663, tp12663, tm12663, ep12663, em12663, dsL]
  · norm_num [world12663, agent12663, scalar12663, tp12663, tm12663, ep12663, em12663, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12663, agent12663, tp12663, tm12663, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12663, agent12663, tp12663, tm12663, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12663, agent12663, scalar12663, tp12663, tm12663, ep12663, em12663, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12663, agent12663, tp12663, tm12663, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12663, agent12663, scalar12663, tp12663, tm12663, ep12663, em12663, dsL]

theorem tails12663 :
    exp (-((12663:ℝ)*ep12663)) ≤ scalar12663.upperTail ∧
    exp (-((12663:ℝ)*em12663)) ≤ scalar12663.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12663:ℝ)) (by norm_num [ep12663]) ?_)
      (show bp12663^8 ≤ scalar12663.upperTail by norm_num [bp12663, scalar12663])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12663, bp12663, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12663:ℝ)) (by norm_num [em12663]) ?_)
      (show bm12663^8 ≤ scalar12663.lowerTail by norm_num [bm12663, scalar12663])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12663, bm12663, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12663 :
    agent12663.root+dsL+scalar12663.worldRadius < √(1/100/aL) ∧
    2*(agent12663.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12663, agent12663, scalar12663, tp12663, tm12663, ep12663, em12663, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12663, agent12663, scalar12663, tp12663, tm12663, ep12663, em12663, dsL]

noncomputable def master12663 : MasterCertificate 12663 world12663 agent12663 :=
  master scalar12663 dsL tp12663 tm12663 ep12663 em12663
    (by norm_num [dsL]) (by norm_num [tp12663]) (by norm_num [tm12663])
    (by norm_num [ep12663]) (by norm_num [em12663])
    positive12663 negative12663 tails12663.1 tails12663.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12663.1 tailGuards12663.2

theorem preserves12663 : master12663.toScalarCertificate = scalar12663 := rfl

noncomputable def tp12664 : ℝ := (578276853 / 2500000000)
noncomputable def tm12664 : ℝ := (-((1211077511 / 2000000000)))
noncomputable def ep12664 : ℝ := (51324027000160711 / 100000000000000000000)
noncomputable def em12664 : ℝ := (25010988333938281 / 50000000000000000000)
noncomputable def bp12664 : ℝ := (44376534992409194667 / 100000000000000000000)
noncomputable def bm12664 : ℝ := (22650345706114099291 / 50000000000000000000)

theorem positive12664 :
    Eplus aL (agent12664.root+dsL) scalar12664.worldRadius world12664.frame
      agent12664.frame tp12664 ≤ -ep12664 := by
  apply positive_check (eT := (57792140715776370771 / 50000000000000000000)) (y := (37835338381430341573 / 100000000000000000000)) (u := (72993937462622385987 / 50000000000000000000))
  · norm_num [world12664, agent12664, scalar12664, tp12664, tm12664, ep12664, em12664, dsL]
  · norm_num [world12664, agent12664, scalar12664, tp12664, tm12664, ep12664, em12664, dsL]
  · norm_num [world12664, agent12664, scalar12664, tp12664, tm12664, ep12664, em12664, dsL]
  · norm_num [world12664, agent12664, scalar12664, tp12664, tm12664, ep12664, em12664, dsL]
  · norm_num [world12664, agent12664, scalar12664, tp12664, tm12664, ep12664, em12664, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12664, agent12664, tp12664, tm12664, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12664, agent12664, scalar12664, tp12664, tm12664, ep12664, em12664, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12664, agent12664, tp12664, tm12664, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12664, agent12664, scalar12664, tp12664, tm12664, ep12664, em12664, dsL]

theorem negative12664 :
    Eminus aL (agent12664.root+dsL) scalar12664.worldRadius world12664.frame
      agent12664.frame tm12664 ≤ -em12664 := by
  apply negative_check (lo := (68444713557252603423 / 100000000000000000000)) (hi := (2138897298664143857 / 3125000000000000000))
    (y := (-((71692234884684327067 / 100000000000000000000)))) (u := (4882526172118199107 / 10000000000000000000))
  · norm_num [world12664, agent12664, scalar12664, tp12664, tm12664, ep12664, em12664, dsL]
  · norm_num [world12664, agent12664, scalar12664, tp12664, tm12664, ep12664, em12664, dsL]
  · norm_num [world12664, agent12664, scalar12664, tp12664, tm12664, ep12664, em12664, dsL]
  · norm_num [world12664, agent12664, scalar12664, tp12664, tm12664, ep12664, em12664, dsL]
  · norm_num [world12664, agent12664, scalar12664, tp12664, tm12664, ep12664, em12664, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12664, agent12664, tp12664, tm12664, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12664, agent12664, tp12664, tm12664, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12664, agent12664, scalar12664, tp12664, tm12664, ep12664, em12664, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12664, agent12664, tp12664, tm12664, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12664, agent12664, scalar12664, tp12664, tm12664, ep12664, em12664, dsL]

theorem tails12664 :
    exp (-((12664:ℝ)*ep12664)) ≤ scalar12664.upperTail ∧
    exp (-((12664:ℝ)*em12664)) ≤ scalar12664.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12664:ℝ)) (by norm_num [ep12664]) ?_)
      (show bp12664^8 ≤ scalar12664.upperTail by norm_num [bp12664, scalar12664])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12664, bp12664, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12664:ℝ)) (by norm_num [em12664]) ?_)
      (show bm12664^8 ≤ scalar12664.lowerTail by norm_num [bm12664, scalar12664])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12664, bm12664, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12664 :
    agent12664.root+dsL+scalar12664.worldRadius < √(1/100/aL) ∧
    2*(agent12664.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12664, agent12664, scalar12664, tp12664, tm12664, ep12664, em12664, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12664, agent12664, scalar12664, tp12664, tm12664, ep12664, em12664, dsL]

noncomputable def master12664 : MasterCertificate 12664 world12664 agent12664 :=
  master scalar12664 dsL tp12664 tm12664 ep12664 em12664
    (by norm_num [dsL]) (by norm_num [tp12664]) (by norm_num [tm12664])
    (by norm_num [ep12664]) (by norm_num [em12664])
    positive12664 negative12664 tails12664.1 tails12664.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12664.1 tailGuards12664.2

theorem preserves12664 : master12664.toScalarCertificate = scalar12664 := rfl

noncomputable def tp12665 : ℝ := (1156596931 / 5000000000)
noncomputable def tm12665 : ℝ := (-((6055573249 / 10000000000)))
noncomputable def ep12665 : ℝ := (51326692672044983 / 100000000000000000000)
noncomputable def em12665 : ℝ := (50024265670963733 / 100000000000000000000)
noncomputable def bp12665 : ℝ := (11092953883692390163 / 25000000000000000000)
noncomputable def bm12665 : ℝ := (5662027187376186057 / 12500000000000000000)

theorem positive12665 :
    Eplus aL (agent12665.root+dsL) scalar12665.worldRadius world12665.frame
      agent12665.frame tp12665 ≤ -ep12665 := by
  apply positive_check (eT := (57792267414767331319 / 50000000000000000000)) (y := (18918073051349042727 / 50000000000000000000)) (u := (4562157940785034607 / 3125000000000000000))
  · norm_num [world12665, agent12665, scalar12665, tp12665, tm12665, ep12665, em12665, dsL]
  · norm_num [world12665, agent12665, scalar12665, tp12665, tm12665, ep12665, em12665, dsL]
  · norm_num [world12665, agent12665, scalar12665, tp12665, tm12665, ep12665, em12665, dsL]
  · norm_num [world12665, agent12665, scalar12665, tp12665, tm12665, ep12665, em12665, dsL]
  · norm_num [world12665, agent12665, scalar12665, tp12665, tm12665, ep12665, em12665, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12665, agent12665, tp12665, tm12665, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12665, agent12665, scalar12665, tp12665, tm12665, ep12665, em12665, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12665, agent12665, tp12665, tm12665, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12665, agent12665, scalar12665, tp12665, tm12665, ep12665, em12665, dsL]

theorem negative12665 :
    Eminus aL (agent12665.root+dsL) scalar12665.worldRadius world12665.frame
      agent12665.frame tm12665 ≤ -em12665 := by
  apply negative_check (lo := (13688898962722144691 / 20000000000000000000)) (hi := (534722615731333777 / 781250000000000000))
    (y := (-((35846161751621639427 / 50000000000000000000)))) (u := (48825218452957821161 / 100000000000000000000))
  · norm_num [world12665, agent12665, scalar12665, tp12665, tm12665, ep12665, em12665, dsL]
  · norm_num [world12665, agent12665, scalar12665, tp12665, tm12665, ep12665, em12665, dsL]
  · norm_num [world12665, agent12665, scalar12665, tp12665, tm12665, ep12665, em12665, dsL]
  · norm_num [world12665, agent12665, scalar12665, tp12665, tm12665, ep12665, em12665, dsL]
  · norm_num [world12665, agent12665, scalar12665, tp12665, tm12665, ep12665, em12665, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12665, agent12665, tp12665, tm12665, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12665, agent12665, tp12665, tm12665, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12665, agent12665, scalar12665, tp12665, tm12665, ep12665, em12665, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12665, agent12665, tp12665, tm12665, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12665, agent12665, scalar12665, tp12665, tm12665, ep12665, em12665, dsL]

theorem tails12665 :
    exp (-((12665:ℝ)*ep12665)) ≤ scalar12665.upperTail ∧
    exp (-((12665:ℝ)*em12665)) ≤ scalar12665.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12665:ℝ)) (by norm_num [ep12665]) ?_)
      (show bp12665^8 ≤ scalar12665.upperTail by norm_num [bp12665, scalar12665])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12665, bp12665, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12665:ℝ)) (by norm_num [em12665]) ?_)
      (show bm12665^8 ≤ scalar12665.lowerTail by norm_num [bm12665, scalar12665])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12665, bm12665, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12665 :
    agent12665.root+dsL+scalar12665.worldRadius < √(1/100/aL) ∧
    2*(agent12665.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12665, agent12665, scalar12665, tp12665, tm12665, ep12665, em12665, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12665, agent12665, scalar12665, tp12665, tm12665, ep12665, em12665, dsL]

noncomputable def master12665 : MasterCertificate 12665 world12665 agent12665 :=
  master scalar12665 dsL tp12665 tm12665 ep12665 em12665
    (by norm_num [dsL]) (by norm_num [tp12665]) (by norm_num [tm12665])
    (by norm_num [ep12665]) (by norm_num [em12665])
    positive12665 negative12665 tails12665.1 tails12665.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12665.1 tailGuards12665.2

theorem preserves12665 : master12665.toScalarCertificate = scalar12665 := rfl

noncomputable def tp12666 : ℝ := (2313280353 / 10000000000)
noncomputable def tm12666 : ℝ := (-((378484933 / 625000000)))
noncomputable def ep12666 : ℝ := (51329356904654723 / 100000000000000000000)
noncomputable def em12666 : ℝ := (50026553328140161 / 100000000000000000000)
noncomputable def bp12666 : ℝ := (4436709729438230757 / 10000000000000000000)
noncomputable def bm12666 : ℝ := (45291744733581515729 / 100000000000000000000)

theorem positive12666 :
    Eplus aL (agent12666.root+dsL) scalar12666.worldRadius world12666.frame
      agent12666.frame tp12666 ≤ -ep12666 := by
  apply positive_check (eT := (3612024642403181823 / 3125000000000000000)) (y := (37836954918334431221 / 100000000000000000000)) (u := (36497558723048312931 / 25000000000000000000))
  · norm_num [world12666, agent12666, scalar12666, tp12666, tm12666, ep12666, em12666, dsL]
  · norm_num [world12666, agent12666, scalar12666, tp12666, tm12666, ep12666, em12666, dsL]
  · norm_num [world12666, agent12666, scalar12666, tp12666, tm12666, ep12666, em12666, dsL]
  · norm_num [world12666, agent12666, scalar12666, tp12666, tm12666, ep12666, em12666, dsL]
  · norm_num [world12666, agent12666, scalar12666, tp12666, tm12666, ep12666, em12666, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12666, agent12666, tp12666, tm12666, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12666, agent12666, scalar12666, tp12666, tm12666, ep12666, em12666, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12666, agent12666, tp12666, tm12666, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12666, agent12666, scalar12666, tp12666, tm12666, ep12666, em12666, dsL]

theorem negative12666 :
    Eminus aL (agent12666.root+dsL) scalar12666.worldRadius world12666.frame
      agent12666.frame tm12666 ≤ -em12666 := by
  apply negative_check (lo := (68444276077410495651 / 100000000000000000000)) (hi := (17111069019352623913 / 25000000000000000000))
    (y := (-((35846206212495077751 / 50000000000000000000)))) (u := (12206293759184989921 / 25000000000000000000))
  · norm_num [world12666, agent12666, scalar12666, tp12666, tm12666, ep12666, em12666, dsL]
  · norm_num [world12666, agent12666, scalar12666, tp12666, tm12666, ep12666, em12666, dsL]
  · norm_num [world12666, agent12666, scalar12666, tp12666, tm12666, ep12666, em12666, dsL]
  · norm_num [world12666, agent12666, scalar12666, tp12666, tm12666, ep12666, em12666, dsL]
  · norm_num [world12666, agent12666, scalar12666, tp12666, tm12666, ep12666, em12666, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12666, agent12666, tp12666, tm12666, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12666, agent12666, tp12666, tm12666, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12666, agent12666, scalar12666, tp12666, tm12666, ep12666, em12666, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12666, agent12666, tp12666, tm12666, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12666, agent12666, scalar12666, tp12666, tm12666, ep12666, em12666, dsL]

theorem tails12666 :
    exp (-((12666:ℝ)*ep12666)) ≤ scalar12666.upperTail ∧
    exp (-((12666:ℝ)*em12666)) ≤ scalar12666.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12666:ℝ)) (by norm_num [ep12666]) ?_)
      (show bp12666^8 ≤ scalar12666.upperTail by norm_num [bp12666, scalar12666])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12666, bp12666, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12666:ℝ)) (by norm_num [em12666]) ?_)
      (show bm12666^8 ≤ scalar12666.lowerTail by norm_num [bm12666, scalar12666])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12666, bm12666, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12666 :
    agent12666.root+dsL+scalar12666.worldRadius < √(1/100/aL) ∧
    2*(agent12666.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12666, agent12666, scalar12666, tp12666, tm12666, ep12666, em12666, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12666, agent12666, scalar12666, tp12666, tm12666, ep12666, em12666, dsL]

noncomputable def master12666 : MasterCertificate 12666 world12666 agent12666 :=
  master scalar12666 dsL tp12666 tm12666 ep12666 em12666
    (by norm_num [dsL]) (by norm_num [tp12666]) (by norm_num [tm12666])
    (by norm_num [ep12666]) (by norm_num [em12666])
    positive12666 negative12666 tails12666.1 tails12666.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12666.1 tailGuards12666.2

theorem preserves12666 : master12666.toScalarCertificate = scalar12666 := rfl

noncomputable def tp12667 : ℝ := (5783417 / 25000000)
noncomputable def tm12667 : ℝ := (-((3027972277 / 5000000000)))
noncomputable def ep12667 : ℝ := (12833004928845057 / 25000000000000000000)
noncomputable def em12667 : ℝ := (50028839661186389 / 100000000000000000000)
noncomputable def bp12667 : ℝ := (44362380258989956717 / 100000000000000000000)
noncomputable def bm12667 : ℝ := (1811490924012078967 / 4000000000000000000)

theorem positive12667 :
    Eplus aL (agent12667.root+dsL) scalar12667.worldRadius world12667.frame
      agent12667.frame tp12667 ≤ -ep12667 := by
  apply positive_check (eT := (28896260499626323883 / 25000000000000000000)) (y := (3783776343660066663 / 10000000000000000000)) (u := (145991415254680991817 / 100000000000000000000))
  · norm_num [world12667, agent12667, scalar12667, tp12667, tm12667, ep12667, em12667, dsL]
  · norm_num [world12667, agent12667, scalar12667, tp12667, tm12667, ep12667, em12667, dsL]
  · norm_num [world12667, agent12667, scalar12667, tp12667, tm12667, ep12667, em12667, dsL]
  · norm_num [world12667, agent12667, scalar12667, tp12667, tm12667, ep12667, em12667, dsL]
  · norm_num [world12667, agent12667, scalar12667, tp12667, tm12667, ep12667, em12667, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12667, agent12667, tp12667, tm12667, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12667, agent12667, scalar12667, tp12667, tm12667, ep12667, em12667, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12667, agent12667, tp12667, tm12667, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12667, agent12667, scalar12667, tp12667, tm12667, ep12667, em12667, dsL]

theorem negative12667 :
    Eminus aL (agent12667.root+dsL) scalar12667.worldRadius world12667.frame
      agent12667.frame tm12667 ≤ -em12667 := by
  apply negative_check (lo := (68444057511517233393 / 100000000000000000000)) (hi := (34222028755758616697 / 50000000000000000000))
    (y := (-((7169250169208780301 / 10000000000000000000)))) (u := (9765026290388547303 / 20000000000000000000))
  · norm_num [world12667, agent12667, scalar12667, tp12667, tm12667, ep12667, em12667, dsL]
  · norm_num [world12667, agent12667, scalar12667, tp12667, tm12667, ep12667, em12667, dsL]
  · norm_num [world12667, agent12667, scalar12667, tp12667, tm12667, ep12667, em12667, dsL]
  · norm_num [world12667, agent12667, scalar12667, tp12667, tm12667, ep12667, em12667, dsL]
  · norm_num [world12667, agent12667, scalar12667, tp12667, tm12667, ep12667, em12667, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12667, agent12667, tp12667, tm12667, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12667, agent12667, tp12667, tm12667, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12667, agent12667, scalar12667, tp12667, tm12667, ep12667, em12667, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12667, agent12667, tp12667, tm12667, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12667, agent12667, scalar12667, tp12667, tm12667, ep12667, em12667, dsL]

theorem tails12667 :
    exp (-((12667:ℝ)*ep12667)) ≤ scalar12667.upperTail ∧
    exp (-((12667:ℝ)*em12667)) ≤ scalar12667.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12667:ℝ)) (by norm_num [ep12667]) ?_)
      (show bp12667^8 ≤ scalar12667.upperTail by norm_num [bp12667, scalar12667])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12667, bp12667, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12667:ℝ)) (by norm_num [em12667]) ?_)
      (show bm12667^8 ≤ scalar12667.lowerTail by norm_num [bm12667, scalar12667])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12667, bm12667, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12667 :
    agent12667.root+dsL+scalar12667.worldRadius < √(1/100/aL) ∧
    2*(agent12667.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12667, agent12667, scalar12667, tp12667, tm12667, ep12667, em12667, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12667, agent12667, scalar12667, tp12667, tm12667, ep12667, em12667, dsL]

noncomputable def master12667 : MasterCertificate 12667 world12667 agent12667 :=
  master scalar12667 dsL tp12667 tm12667 ep12667 em12667
    (by norm_num [dsL]) (by norm_num [tp12667]) (by norm_num [tm12667])
    (by norm_num [ep12667]) (by norm_num [em12667])
    positive12667 negative12667 tails12667.1 tails12667.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12667.1 tailGuards12667.2

theorem preserves12667 : master12667.toScalarCertificate = scalar12667 := rfl

noncomputable def tp12668 : ℝ := (2313453201 / 10000000000)
noncomputable def tm12668 : ℝ := (-((605613009 / 1000000000)))
noncomputable def ep12668 : ℝ := (12833670395008501 / 25000000000000000000)
noncomputable def em12668 : ℝ := (50031125110089773 / 100000000000000000000)
noncomputable def bp12668 : ℝ := (44357664094338937391 / 100000000000000000000)
noncomputable def bm12668 : ℝ := (4528280228365325771 / 10000000000000000000)

theorem positive12668 :
    Eplus aL (agent12668.root+dsL) scalar12668.worldRadius world12668.frame
      agent12668.frame tp12668 ≤ -ep12668 := by
  apply positive_check (eT := (28896323784961192013 / 25000000000000000000)) (y := (18919285786598459983 / 50000000000000000000)) (u := (72996297534751152159 / 50000000000000000000))
  · norm_num [world12668, agent12668, scalar12668, tp12668, tm12668, ep12668, em12668, dsL]
  · norm_num [world12668, agent12668, scalar12668, tp12668, tm12668, ep12668, em12668, dsL]
  · norm_num [world12668, agent12668, scalar12668, tp12668, tm12668, ep12668, em12668, dsL]
  · norm_num [world12668, agent12668, scalar12668, tp12668, tm12668, ep12668, em12668, dsL]
  · norm_num [world12668, agent12668, scalar12668, tp12668, tm12668, ep12668, em12668, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12668, agent12668, tp12668, tm12668, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12668, agent12668, scalar12668, tp12668, tm12668, ep12668, em12668, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12668, agent12668, tp12668, tm12668, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12668, agent12668, scalar12668, tp12668, tm12668, ep12668, em12668, dsL]

theorem negative12668 :
    Eminus aL (agent12668.root+dsL) scalar12668.worldRadius world12668.frame
      agent12668.frame tm12668 ≤ -em12668 := by
  apply negative_check (lo := (68443839274536081127 / 100000000000000000000)) (hi := (8555479909317010141 / 12500000000000000000))
    (y := (-((71692591072065655999 / 100000000000000000000)))) (u := (48825087812070560733 / 100000000000000000000))
  · norm_num [world12668, agent12668, scalar12668, tp12668, tm12668, ep12668, em12668, dsL]
  · norm_num [world12668, agent12668, scalar12668, tp12668, tm12668, ep12668, em12668, dsL]
  · norm_num [world12668, agent12668, scalar12668, tp12668, tm12668, ep12668, em12668, dsL]
  · norm_num [world12668, agent12668, scalar12668, tp12668, tm12668, ep12668, em12668, dsL]
  · norm_num [world12668, agent12668, scalar12668, tp12668, tm12668, ep12668, em12668, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12668, agent12668, tp12668, tm12668, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12668, agent12668, tp12668, tm12668, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12668, agent12668, scalar12668, tp12668, tm12668, ep12668, em12668, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12668, agent12668, tp12668, tm12668, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12668, agent12668, scalar12668, tp12668, tm12668, ep12668, em12668, dsL]

theorem tails12668 :
    exp (-((12668:ℝ)*ep12668)) ≤ scalar12668.upperTail ∧
    exp (-((12668:ℝ)*em12668)) ≤ scalar12668.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12668:ℝ)) (by norm_num [ep12668]) ?_)
      (show bp12668^8 ≤ scalar12668.upperTail by norm_num [bp12668, scalar12668])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12668, bp12668, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12668:ℝ)) (by norm_num [em12668]) ?_)
      (show bm12668^8 ≤ scalar12668.lowerTail by norm_num [bm12668, scalar12668])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12668, bm12668, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12668 :
    agent12668.root+dsL+scalar12668.worldRadius < √(1/100/aL) ∧
    2*(agent12668.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12668, agent12668, scalar12668, tp12668, tm12668, ep12668, em12668, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12668, agent12668, scalar12668, tp12668, tm12668, ep12668, em12668, dsL]

noncomputable def master12668 : MasterCertificate 12668 world12668 agent12668 :=
  master scalar12668 dsL tp12668 tm12668 ep12668 em12668
    (by norm_num [dsL]) (by norm_num [tp12668]) (by norm_num [tm12668])
    (by norm_num [ep12668]) (by norm_num [em12668])
    positive12668 negative12668 tails12668.1 tails12668.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12668.1 tailGuards12668.2

theorem preserves12668 : master12668.toScalarCertificate = scalar12668 := rfl

noncomputable def tp12669 : ℝ := (57838489 / 250000000)
noncomputable def tm12669 : ℝ := (-((3028157713 / 5000000000)))
noncomputable def ep12669 : ℝ := (51337342164712349 / 100000000000000000000)
noncomputable def em12669 : ℝ := (25016704691612877 / 50000000000000000000)
noncomputable def bp12669 : ℝ := (5544118629368033941 / 12500000000000000000)
noncomputable def bm12669 : ℝ := (11319583123184243783 / 25000000000000000000)

theorem positive12669 :
    Eplus aL (agent12669.root+dsL) scalar12669.worldRadius world12669.frame
      agent12669.frame tp12669 ≤ -ep12669 := by
  apply positive_check (eT := (11558554800991915957 / 10000000000000000000)) (y := (18919689647746839397 / 50000000000000000000)) (u := (72996887144503350269 / 50000000000000000000))
  · norm_num [world12669, agent12669, scalar12669, tp12669, tm12669, ep12669, em12669, dsL]
  · norm_num [world12669, agent12669, scalar12669, tp12669, tm12669, ep12669, em12669, dsL]
  · norm_num [world12669, agent12669, scalar12669, tp12669, tm12669, ep12669, em12669, dsL]
  · norm_num [world12669, agent12669, scalar12669, tp12669, tm12669, ep12669, em12669, dsL]
  · norm_num [world12669, agent12669, scalar12669, tp12669, tm12669, ep12669, em12669, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12669, agent12669, tp12669, tm12669, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12669, agent12669, scalar12669, tp12669, tm12669, ep12669, em12669, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12669, agent12669, tp12669, tm12669, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12669, agent12669, scalar12669, tp12669, tm12669, ep12669, em12669, dsL]

theorem negative12669 :
    Eminus aL (agent12669.root+dsL) scalar12669.worldRadius world12669.frame
      agent12669.frame tm12669 ≤ -em12669 := by
  apply negative_check (lo := (34221810918866916109 / 50000000000000000000)) (hi := (68443621837733832219 / 100000000000000000000))
    (y := (-((35846339539064253571 / 50000000000000000000)))) (u := (4882504484305200139 / 10000000000000000000))
  · norm_num [world12669, agent12669, scalar12669, tp12669, tm12669, ep12669, em12669, dsL]
  · norm_num [world12669, agent12669, scalar12669, tp12669, tm12669, ep12669, em12669, dsL]
  · norm_num [world12669, agent12669, scalar12669, tp12669, tm12669, ep12669, em12669, dsL]
  · norm_num [world12669, agent12669, scalar12669, tp12669, tm12669, ep12669, em12669, dsL]
  · norm_num [world12669, agent12669, scalar12669, tp12669, tm12669, ep12669, em12669, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12669, agent12669, tp12669, tm12669, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12669, agent12669, tp12669, tm12669, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12669, agent12669, scalar12669, tp12669, tm12669, ep12669, em12669, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12669, agent12669, tp12669, tm12669, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12669, agent12669, scalar12669, tp12669, tm12669, ep12669, em12669, dsL]

theorem tails12669 :
    exp (-((12669:ℝ)*ep12669)) ≤ scalar12669.upperTail ∧
    exp (-((12669:ℝ)*em12669)) ≤ scalar12669.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12669:ℝ)) (by norm_num [ep12669]) ?_)
      (show bp12669^8 ≤ scalar12669.upperTail by norm_num [bp12669, scalar12669])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12669, bp12669, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12669:ℝ)) (by norm_num [em12669]) ?_)
      (show bm12669^8 ≤ scalar12669.lowerTail by norm_num [bm12669, scalar12669])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12669, bm12669, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12669 :
    agent12669.root+dsL+scalar12669.worldRadius < √(1/100/aL) ∧
    2*(agent12669.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12669, agent12669, scalar12669, tp12669, tm12669, ep12669, em12669, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12669, agent12669, scalar12669, tp12669, tm12669, ep12669, em12669, dsL]

noncomputable def master12669 : MasterCertificate 12669 world12669 agent12669 :=
  master scalar12669 dsL tp12669 tm12669 ep12669 em12669
    (by norm_num [dsL]) (by norm_num [tp12669]) (by norm_num [tm12669])
    (by norm_num [ep12669]) (by norm_num [em12669])
    positive12669 negative12669 tails12669.1 tails12669.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12669.1 tailGuards12669.2

theorem preserves12669 : master12669.toScalarCertificate = scalar12669 := rfl

noncomputable def tp12670 : ℝ := (578425129 / 2500000000)
noncomputable def tm12670 : ℝ := (-((1211345269 / 2000000000)))
noncomputable def ep12670 : ℝ := (3208839342427099 / 6250000000000000000)
noncomputable def em12670 : ℝ := (10007449550607277 / 20000000000000000000)
noncomputable def bp12670 : ℝ := (22173616054016193419 / 50000000000000000000)
noncomputable def bm12670 : ℝ := (22636374286166206573 / 50000000000000000000)

theorem positive12670 :
    Eplus aL (agent12670.root+dsL) scalar12670.worldRadius world12670.frame
      agent12670.frame tp12670 ≤ -ep12670 := by
  apply positive_check (eT := (115586340710350236139 / 100000000000000000000)) (y := (18919730114008062057 / 50000000000000000000)) (u := (145993892445498659267 / 100000000000000000000))
  · norm_num [world12670, agent12670, scalar12670, tp12670, tm12670, ep12670, em12670, dsL]
  · norm_num [world12670, agent12670, scalar12670, tp12670, tm12670, ep12670, em12670, dsL]
  · norm_num [world12670, agent12670, scalar12670, tp12670, tm12670, ep12670, em12670, dsL]
  · norm_num [world12670, agent12670, scalar12670, tp12670, tm12670, ep12670, em12670, dsL]
  · norm_num [world12670, agent12670, scalar12670, tp12670, tm12670, ep12670, em12670, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12670, agent12670, tp12670, tm12670, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12670, agent12670, scalar12670, tp12670, tm12670, ep12670, em12670, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12670, agent12670, tp12670, tm12670, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12670, agent12670, scalar12670, tp12670, tm12670, ep12670, em12670, dsL]

theorem negative12670 :
    Eminus aL (agent12670.root+dsL) scalar12670.worldRadius world12670.frame
      agent12670.frame tm12670 ≤ -em12670 := by
  apply negative_check (lo := (68442437761282000043 / 100000000000000000000)) (hi := (17110609440320500011 / 25000000000000000000))
    (y := (-((17922713910265360277 / 25000000000000000000)))) (u := (48825935145134705637 / 100000000000000000000))
  · norm_num [world12670, agent12670, scalar12670, tp12670, tm12670, ep12670, em12670, dsL]
  · norm_num [world12670, agent12670, scalar12670, tp12670, tm12670, ep12670, em12670, dsL]
  · norm_num [world12670, agent12670, scalar12670, tp12670, tm12670, ep12670, em12670, dsL]
  · norm_num [world12670, agent12670, scalar12670, tp12670, tm12670, ep12670, em12670, dsL]
  · norm_num [world12670, agent12670, scalar12670, tp12670, tm12670, ep12670, em12670, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12670, agent12670, tp12670, tm12670, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12670, agent12670, tp12670, tm12670, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12670, agent12670, scalar12670, tp12670, tm12670, ep12670, em12670, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12670, agent12670, tp12670, tm12670, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12670, agent12670, scalar12670, tp12670, tm12670, ep12670, em12670, dsL]

theorem tails12670 :
    exp (-((12670:ℝ)*ep12670)) ≤ scalar12670.upperTail ∧
    exp (-((12670:ℝ)*em12670)) ≤ scalar12670.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12670:ℝ)) (by norm_num [ep12670]) ?_)
      (show bp12670^8 ≤ scalar12670.upperTail by norm_num [bp12670, scalar12670])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12670, bp12670, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12670:ℝ)) (by norm_num [em12670]) ?_)
      (show bm12670^8 ≤ scalar12670.lowerTail by norm_num [bm12670, scalar12670])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12670, bm12670, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12670 :
    agent12670.root+dsL+scalar12670.worldRadius < √(1/100/aL) ∧
    2*(agent12670.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12670, agent12670, scalar12670, tp12670, tm12670, ep12670, em12670, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12670, agent12670, scalar12670, tp12670, tm12670, ep12670, em12670, dsL]

noncomputable def master12670 : MasterCertificate 12670 world12670 agent12670 :=
  master scalar12670 dsL tp12670 tm12670 ep12670 em12670
    (by norm_num [dsL]) (by norm_num [tp12670]) (by norm_num [tm12670])
    (by norm_num [ep12670]) (by norm_num [em12670])
    positive12670 negative12670 tails12670.1 tails12670.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12670.1 tailGuards12670.2

theorem preserves12670 : master12670.toScalarCertificate = scalar12670 := rfl

noncomputable def tp12671 : ℝ := (578446707 / 2500000000)
noncomputable def tm12671 : ℝ := (-((1514227877 / 2500000000)))
noncomputable def ep12671 : ℝ := (51344086543059041 / 100000000000000000000)
noncomputable def em12671 : ℝ := (50039528778818059 / 100000000000000000000)
noncomputable def bp12671 : ℝ := (11085629990268499263 / 25000000000000000000)
noncomputable def bm12671 : ℝ := (4526828149716698423 / 10000000000000000000)

theorem positive12671 :
    Eplus aL (agent12671.root+dsL) scalar12671.worldRadius world12671.frame
      agent12671.frame tp12671 ≤ -ep12671 := by
  apply positive_check (eT := (57793296647401624431 / 50000000000000000000)) (y := (1892013401929425801 / 5000000000000000000)) (u := (29199014360872073369 / 20000000000000000000))
  · norm_num [world12671, agent12671, scalar12671, tp12671, tm12671, ep12671, em12671, dsL]
  · norm_num [world12671, agent12671, scalar12671, tp12671, tm12671, ep12671, em12671, dsL]
  · norm_num [world12671, agent12671, scalar12671, tp12671, tm12671, ep12671, em12671, dsL]
  · norm_num [world12671, agent12671, scalar12671, tp12671, tm12671, ep12671, em12671, dsL]
  · norm_num [world12671, agent12671, scalar12671, tp12671, tm12671, ep12671, em12671, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12671, agent12671, tp12671, tm12671, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12671, agent12671, scalar12671, tp12671, tm12671, ep12671, em12671, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12671, agent12671, tp12671, tm12671, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12671, agent12671, scalar12671, tp12671, tm12671, ep12671, em12671, dsL]

theorem negative12671 :
    Eminus aL (agent12671.root+dsL) scalar12671.worldRadius world12671.frame
      agent12671.frame tm12671 ≤ -em12671 := by
  apply negative_check (lo := (68442220976663872009 / 100000000000000000000)) (hi := (6844222097666387201 / 10000000000000000000))
    (y := (-((71690943439177787923 / 100000000000000000000)))) (u := (9765178455380435649 / 20000000000000000000))
  · norm_num [world12671, agent12671, scalar12671, tp12671, tm12671, ep12671, em12671, dsL]
  · norm_num [world12671, agent12671, scalar12671, tp12671, tm12671, ep12671, em12671, dsL]
  · norm_num [world12671, agent12671, scalar12671, tp12671, tm12671, ep12671, em12671, dsL]
  · norm_num [world12671, agent12671, scalar12671, tp12671, tm12671, ep12671, em12671, dsL]
  · norm_num [world12671, agent12671, scalar12671, tp12671, tm12671, ep12671, em12671, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12671, agent12671, tp12671, tm12671, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12671, agent12671, tp12671, tm12671, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12671, agent12671, scalar12671, tp12671, tm12671, ep12671, em12671, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12671, agent12671, tp12671, tm12671, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12671, agent12671, scalar12671, tp12671, tm12671, ep12671, em12671, dsL]

theorem tails12671 :
    exp (-((12671:ℝ)*ep12671)) ≤ scalar12671.upperTail ∧
    exp (-((12671:ℝ)*em12671)) ≤ scalar12671.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12671:ℝ)) (by norm_num [ep12671]) ?_)
      (show bp12671^8 ≤ scalar12671.upperTail by norm_num [bp12671, scalar12671])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12671, bp12671, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12671:ℝ)) (by norm_num [em12671]) ?_)
      (show bm12671^8 ≤ scalar12671.lowerTail by norm_num [bm12671, scalar12671])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12671, bm12671, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12671 :
    agent12671.root+dsL+scalar12671.worldRadius < √(1/100/aL) ∧
    2*(agent12671.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12671, agent12671, scalar12671, tp12671, tm12671, ep12671, em12671, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12671, agent12671, scalar12671, tp12671, tm12671, ep12671, em12671, dsL]

noncomputable def master12671 : MasterCertificate 12671 world12671 agent12671 :=
  master scalar12671 dsL tp12671 tm12671 ep12671 em12671
    (by norm_num [dsL]) (by norm_num [tp12671]) (by norm_num [tm12671])
    (by norm_num [ep12671]) (by norm_num [em12671])
    positive12671 negative12671 tails12671.1 tails12671.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12671.1 tailGuards12671.2

theorem preserves12671 : master12671.toScalarCertificate = scalar12671 := rfl

noncomputable def tp12672 : ℝ := (1156936501 / 5000000000)
noncomputable def tm12672 : ℝ := (-((6057096619 / 10000000000)))
noncomputable def ep12672 : ℝ := (25673371630742571 / 50000000000000000000)
noncomputable def em12672 : ℝ := (50041809487028261 / 100000000000000000000)
noncomputable def bp12672 : ℝ := (44337808263145802961 / 100000000000000000000)
noncomputable def bm12672 : ℝ := (45263814832341350827 / 100000000000000000000)

theorem positive12672 :
    Eplus aL (agent12672.root+dsL) scalar12672.worldRadius world12672.frame
      agent12672.frame tp12672 ≤ -ep12672 := by
  apply positive_check (eT := (115586844913355557701 / 100000000000000000000)) (y := (7568214709651250087 / 20000000000000000000)) (u := (72998123906757297063 / 50000000000000000000))
  · norm_num [world12672, agent12672, scalar12672, tp12672, tm12672, ep12672, em12672, dsL]
  · norm_num [world12672, agent12672, scalar12672, tp12672, tm12672, ep12672, em12672, dsL]
  · norm_num [world12672, agent12672, scalar12672, tp12672, tm12672, ep12672, em12672, dsL]
  · norm_num [world12672, agent12672, scalar12672, tp12672, tm12672, ep12672, em12672, dsL]
  · norm_num [world12672, agent12672, scalar12672, tp12672, tm12672, ep12672, em12672, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12672, agent12672, tp12672, tm12672, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12672, agent12672, scalar12672, tp12672, tm12672, ep12672, em12672, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12672, agent12672, tp12672, tm12672, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12672, agent12672, scalar12672, tp12672, tm12672, ep12672, em12672, dsL]

theorem negative12672 :
    Eminus aL (agent12672.root+dsL) scalar12672.worldRadius world12672.frame
      agent12672.frame tm12672 ≤ -em12672 := by
  apply negative_check (lo := (68442004358005415869 / 100000000000000000000)) (hi := (6844200435800541587 / 10000000000000000000))
    (y := (-((17922757786808794219 / 25000000000000000000)))) (u := (48825849452679339501 / 100000000000000000000))
  · norm_num [world12672, agent12672, scalar12672, tp12672, tm12672, ep12672, em12672, dsL]
  · norm_num [world12672, agent12672, scalar12672, tp12672, tm12672, ep12672, em12672, dsL]
  · norm_num [world12672, agent12672, scalar12672, tp12672, tm12672, ep12672, em12672, dsL]
  · norm_num [world12672, agent12672, scalar12672, tp12672, tm12672, ep12672, em12672, dsL]
  · norm_num [world12672, agent12672, scalar12672, tp12672, tm12672, ep12672, em12672, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12672, agent12672, tp12672, tm12672, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12672, agent12672, tp12672, tm12672, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12672, agent12672, scalar12672, tp12672, tm12672, ep12672, em12672, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12672, agent12672, tp12672, tm12672, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12672, agent12672, scalar12672, tp12672, tm12672, ep12672, em12672, dsL]

theorem tails12672 :
    exp (-((12672:ℝ)*ep12672)) ≤ scalar12672.upperTail ∧
    exp (-((12672:ℝ)*em12672)) ≤ scalar12672.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12672:ℝ)) (by norm_num [ep12672]) ?_)
      (show bp12672^8 ≤ scalar12672.upperTail by norm_num [bp12672, scalar12672])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12672, bp12672, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12672:ℝ)) (by norm_num [em12672]) ?_)
      (show bm12672^8 ≤ scalar12672.lowerTail by norm_num [bm12672, scalar12672])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12672, bm12672, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12672 :
    agent12672.root+dsL+scalar12672.worldRadius < √(1/100/aL) ∧
    2*(agent12672.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12672, agent12672, scalar12672, tp12672, tm12672, ep12672, em12672, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12672, agent12672, scalar12672, tp12672, tm12672, ep12672, em12672, dsL]

noncomputable def master12672 : MasterCertificate 12672 world12672 agent12672 :=
  master scalar12672 dsL tp12672 tm12672 ep12672 em12672
    (by norm_num [dsL]) (by norm_num [tp12672]) (by norm_num [tm12672])
    (by norm_num [ep12672]) (by norm_num [em12672])
    positive12672 negative12672 tails12672.1 tails12672.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12672.1 tailGuards12672.2

theorem preserves12672 : master12672.toScalarCertificate = scalar12672 := rfl

noncomputable def tp12673 : ℝ := (2892449 / 12500000)
noncomputable def tm12673 : ℝ := (-((6057281541 / 10000000000)))
noncomputable def ep12673 : ℝ := (25674698975024621 / 50000000000000000000)
noncomputable def em12673 : ℝ := (12511022072872929 / 25000000000000000000)
noncomputable def bp12673 : ℝ := (44333098196971748697 / 100000000000000000000)
noncomputable def bm12673 : ℝ := (22629674857553276239 / 50000000000000000000)

theorem positive12673 :
    Eplus aL (agent12673.root+dsL) scalar12673.worldRadius world12673.frame
      agent12673.frame tp12673 ≤ -ep12673 := by
  apply positive_check (eT := (28896774184560403593 / 25000000000000000000)) (y := (7568376030955453887 / 20000000000000000000)) (u := (36499356358379818621 / 25000000000000000000))
  · norm_num [world12673, agent12673, scalar12673, tp12673, tm12673, ep12673, em12673, dsL]
  · norm_num [world12673, agent12673, scalar12673, tp12673, tm12673, ep12673, em12673, dsL]
  · norm_num [world12673, agent12673, scalar12673, tp12673, tm12673, ep12673, em12673, dsL]
  · norm_num [world12673, agent12673, scalar12673, tp12673, tm12673, ep12673, em12673, dsL]
  · norm_num [world12673, agent12673, scalar12673, tp12673, tm12673, ep12673, em12673, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12673, agent12673, tp12673, tm12673, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12673, agent12673, scalar12673, tp12673, tm12673, ep12673, em12673, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12673, agent12673, tp12673, tm12673, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12673, agent12673, scalar12673, tp12673, tm12673, ep12673, em12673, dsL]

theorem negative12673 :
    Eminus aL (agent12673.root+dsL) scalar12673.worldRadius world12673.frame
      agent12673.frame tm12673 ≤ -em12673 := by
  apply negative_check (lo := (8555223561536854397 / 12500000000000000000)) (hi := (68441788492294835177 / 100000000000000000000))
    (y := (-((286764472136430503 / 400000000000000000)))) (u := (24412903514722116793 / 50000000000000000000))
  · norm_num [world12673, agent12673, scalar12673, tp12673, tm12673, ep12673, em12673, dsL]
  · norm_num [world12673, agent12673, scalar12673, tp12673, tm12673, ep12673, em12673, dsL]
  · norm_num [world12673, agent12673, scalar12673, tp12673, tm12673, ep12673, em12673, dsL]
  · norm_num [world12673, agent12673, scalar12673, tp12673, tm12673, ep12673, em12673, dsL]
  · norm_num [world12673, agent12673, scalar12673, tp12673, tm12673, ep12673, em12673, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12673, agent12673, tp12673, tm12673, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12673, agent12673, tp12673, tm12673, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12673, agent12673, scalar12673, tp12673, tm12673, ep12673, em12673, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12673, agent12673, tp12673, tm12673, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12673, agent12673, scalar12673, tp12673, tm12673, ep12673, em12673, dsL]

theorem tails12673 :
    exp (-((12673:ℝ)*ep12673)) ≤ scalar12673.upperTail ∧
    exp (-((12673:ℝ)*em12673)) ≤ scalar12673.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12673:ℝ)) (by norm_num [ep12673]) ?_)
      (show bp12673^8 ≤ scalar12673.upperTail by norm_num [bp12673, scalar12673])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12673, bp12673, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12673:ℝ)) (by norm_num [em12673]) ?_)
      (show bm12673^8 ≤ scalar12673.lowerTail by norm_num [bm12673, scalar12673])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12673, bm12673, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12673 :
    agent12673.root+dsL+scalar12673.worldRadius < √(1/100/aL) ∧
    2*(agent12673.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12673, agent12673, scalar12673, tp12673, tm12673, ep12673, em12673, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12673, agent12673, scalar12673, tp12673, tm12673, ep12673, em12673, dsL]

noncomputable def master12673 : MasterCertificate 12673 world12673 agent12673 :=
  master scalar12673 dsL tp12673 tm12673 ep12673 em12673
    (by norm_num [dsL]) (by norm_num [tp12673]) (by norm_num [tm12673])
    (by norm_num [ep12673]) (by norm_num [em12673])
    positive12673 negative12673 tails12673.1 tails12673.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12673.1 tailGuards12673.2

theorem preserves12673 : master12673.toScalarCertificate = scalar12673 := rfl

noncomputable def tp12674 : ℝ := (1157022697 / 5000000000)
noncomputable def tm12674 : ℝ := (-((6057466487 / 10000000000)))
noncomputable def ep12674 : ℝ := (25676025681723387 / 50000000000000000000)
noncomputable def em12674 : ℝ := (50046365924509591 / 100000000000000000000)
noncomputable def bp12674 : ℝ := (22164194616236865519 / 50000000000000000000)
noncomputable def bm12674 : ℝ := (45254885620390905487 / 100000000000000000000)

theorem positive12674 :
    Eplus aL (agent12674.root+dsL) scalar12674.worldRadius world12674.frame
      agent12674.frame tp12674 ≤ -ep12674 := by
  apply positive_check (eT := (115587348566860457333 / 100000000000000000000)) (y := (7568537402747050591 / 20000000000000000000)) (u := (145998603431577195181 / 100000000000000000000))
  · norm_num [world12674, agent12674, scalar12674, tp12674, tm12674, ep12674, em12674, dsL]
  · norm_num [world12674, agent12674, scalar12674, tp12674, tm12674, ep12674, em12674, dsL]
  · norm_num [world12674, agent12674, scalar12674, tp12674, tm12674, ep12674, em12674, dsL]
  · norm_num [world12674, agent12674, scalar12674, tp12674, tm12674, ep12674, em12674, dsL]
  · norm_num [world12674, agent12674, scalar12674, tp12674, tm12674, ep12674, em12674, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12674, agent12674, tp12674, tm12674, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12674, agent12674, scalar12674, tp12674, tm12674, ep12674, em12674, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12674, agent12674, tp12674, tm12674, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12674, agent12674, scalar12674, tp12674, tm12674, ep12674, em12674, dsL]

theorem negative12674 :
    Eminus aL (agent12674.root+dsL) scalar12674.worldRadius world12674.frame
      agent12674.frame tm12674 ≤ -em12674 := by
  apply negative_check (lo := (68441572466894700811 / 100000000000000000000)) (hi := (17110393116723675203 / 25000000000000000000))
    (y := (-((17922801431493640837 / 25000000000000000000)))) (u := (48825764213201275301 / 100000000000000000000))
  · norm_num [world12674, agent12674, scalar12674, tp12674, tm12674, ep12674, em12674, dsL]
  · norm_num [world12674, agent12674, scalar12674, tp12674, tm12674, ep12674, em12674, dsL]
  · norm_num [world12674, agent12674, scalar12674, tp12674, tm12674, ep12674, em12674, dsL]
  · norm_num [world12674, agent12674, scalar12674, tp12674, tm12674, ep12674, em12674, dsL]
  · norm_num [world12674, agent12674, scalar12674, tp12674, tm12674, ep12674, em12674, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12674, agent12674, tp12674, tm12674, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12674, agent12674, tp12674, tm12674, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12674, agent12674, scalar12674, tp12674, tm12674, ep12674, em12674, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12674, agent12674, tp12674, tm12674, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12674, agent12674, scalar12674, tp12674, tm12674, ep12674, em12674, dsL]

theorem tails12674 :
    exp (-((12674:ℝ)*ep12674)) ≤ scalar12674.upperTail ∧
    exp (-((12674:ℝ)*em12674)) ≤ scalar12674.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12674:ℝ)) (by norm_num [ep12674]) ?_)
      (show bp12674^8 ≤ scalar12674.upperTail by norm_num [bp12674, scalar12674])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12674, bp12674, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12674:ℝ)) (by norm_num [em12674]) ?_)
      (show bm12674^8 ≤ scalar12674.lowerTail by norm_num [bm12674, scalar12674])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12674, bm12674, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12674 :
    agent12674.root+dsL+scalar12674.worldRadius < √(1/100/aL) ∧
    2*(agent12674.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12674, agent12674, scalar12674, tp12674, tm12674, ep12674, em12674, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12674, agent12674, scalar12674, tp12674, tm12674, ep12674, em12674, dsL]

noncomputable def master12674 : MasterCertificate 12674 world12674 agent12674 :=
  master scalar12674 dsL tp12674 tm12674 ep12674 em12674
    (by norm_num [dsL]) (by norm_num [tp12674]) (by norm_num [tm12674])
    (by norm_num [ep12674]) (by norm_num [em12674])
    positive12674 negative12674 tails12674.1 tails12674.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12674.1 tailGuards12674.2

theorem preserves12674 : master12674.toScalarCertificate = scalar12674 := rfl

end BstLean.Part268
