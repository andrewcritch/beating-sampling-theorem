import BstLean.Part261Checker
import BstLean.Part281Scalar0
namespace BstLean.Part281
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12224 : ℝ := (595045391 / 2500000000)
noncomputable def tm12224 : ℝ := (-((1538820413 / 2500000000)))
noncomputable def ep12224 : ℝ := (54808858464659913 / 100000000000000000000)
noncomputable def em12224 : ℝ := (52824285970419467 / 100000000000000000000)
noncomputable def bp12224 : ℝ := (21640004200537817373 / 50000000000000000000)
noncomputable def bm12224 : ℝ := (5576568118633820417 / 12500000000000000000)

theorem positive12224 :
    Eplus aL (agent12224.root+dsL) scalar12224.worldRadius world12224.frame
      agent12224.frame tp12224 ≤ -ep12224 := by
  apply positive_check (eT := (116246336692177183867 / 100000000000000000000)) (y := (9918216402065097727 / 25000000000000000000)) (u := (148695239981689742149 / 100000000000000000000))
  · norm_num [world12224, agent12224, scalar12224, tp12224, tm12224, ep12224, em12224, dsL]
  · norm_num [world12224, agent12224, scalar12224, tp12224, tm12224, ep12224, em12224, dsL]
  · norm_num [world12224, agent12224, scalar12224, tp12224, tm12224, ep12224, em12224, dsL]
  · norm_num [world12224, agent12224, scalar12224, tp12224, tm12224, ep12224, em12224, dsL]
  · norm_num [world12224, agent12224, scalar12224, tp12224, tm12224, ep12224, em12224, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12224, agent12224, tp12224, tm12224, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12224, agent12224, scalar12224, tp12224, tm12224, ep12224, em12224, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12224, agent12224, tp12224, tm12224, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12224, agent12224, scalar12224, tp12224, tm12224, ep12224, em12224, dsL]

theorem negative12224 :
    Eminus aL (agent12224.root+dsL) scalar12224.worldRadius world12224.frame
      agent12224.frame tm12224 ≤ -em12224 := by
  apply negative_check (lo := (1355050745129886891 / 2000000000000000000)) (hi := (67752537256494344551 / 100000000000000000000))
    (y := (-((14654720152755008089 / 20000000000000000000)))) (u := (9611845709818211141 / 20000000000000000000))
  · norm_num [world12224, agent12224, scalar12224, tp12224, tm12224, ep12224, em12224, dsL]
  · norm_num [world12224, agent12224, scalar12224, tp12224, tm12224, ep12224, em12224, dsL]
  · norm_num [world12224, agent12224, scalar12224, tp12224, tm12224, ep12224, em12224, dsL]
  · norm_num [world12224, agent12224, scalar12224, tp12224, tm12224, ep12224, em12224, dsL]
  · norm_num [world12224, agent12224, scalar12224, tp12224, tm12224, ep12224, em12224, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12224, agent12224, tp12224, tm12224, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12224, agent12224, tp12224, tm12224, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12224, agent12224, scalar12224, tp12224, tm12224, ep12224, em12224, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12224, agent12224, tp12224, tm12224, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12224, agent12224, scalar12224, tp12224, tm12224, ep12224, em12224, dsL]

theorem tails12224 :
    exp (-((12224:ℝ)*ep12224)) ≤ scalar12224.upperTail ∧
    exp (-((12224:ℝ)*em12224)) ≤ scalar12224.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12224:ℝ)) (by norm_num [ep12224]) ?_)
      (show bp12224^8 ≤ scalar12224.upperTail by norm_num [bp12224, scalar12224])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12224, bp12224, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12224:ℝ)) (by norm_num [em12224]) ?_)
      (show bm12224^8 ≤ scalar12224.lowerTail by norm_num [bm12224, scalar12224])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12224, bm12224, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12224 :
    agent12224.root+dsL+scalar12224.worldRadius < √(1/100/aL) ∧
    2*(agent12224.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12224, agent12224, scalar12224, tp12224, tm12224, ep12224, em12224, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12224, agent12224, scalar12224, tp12224, tm12224, ep12224, em12224, dsL]

noncomputable def master12224 : MasterCertificate 12224 world12224 agent12224 :=
  master scalar12224 dsL tp12224 tm12224 ep12224 em12224
    (by norm_num [dsL]) (by norm_num [tp12224]) (by norm_num [tm12224])
    (by norm_num [ep12224]) (by norm_num [em12224])
    positive12224 negative12224 tails12224.1 tails12224.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12224.1 tailGuards12224.2

theorem preserves12224 : master12224.toScalarCertificate = scalar12224 := rfl

noncomputable def tp11883 : ℝ := (241303033 / 1000000000)
noncomputable def tm11883 : ℝ := (-((1560225363 / 2500000000)))
noncomputable def ep11883 : ℝ := (55895450578190363 / 100000000000000000000)
noncomputable def em11883 : ℝ := (53845530672470993 / 100000000000000000000)
noncomputable def bp11883 : ℝ := (21796860734092898883 / 50000000000000000000)
noncomputable def bm11883 : ℝ := (8988304410781037677 / 20000000000000000000)

theorem positive11883 :
    Eplus aL (agent11883.root+dsL) scalar11883.worldRadius world11883.frame
      agent11883.frame tp11883 ≤ -ep11883 := by
  apply positive_check (eT := (116635915557924913803 / 100000000000000000000)) (y := (39716521133972420019 / 100000000000000000000)) (u := (29752033568336130623 / 20000000000000000000))
  · norm_num [world11883, agent11883, scalar11883, tp11883, tm11883, ep11883, em11883, dsL]
  · norm_num [world11883, agent11883, scalar11883, tp11883, tm11883, ep11883, em11883, dsL]
  · norm_num [world11883, agent11883, scalar11883, tp11883, tm11883, ep11883, em11883, dsL]
  · norm_num [world11883, agent11883, scalar11883, tp11883, tm11883, ep11883, em11883, dsL]
  · norm_num [world11883, agent11883, scalar11883, tp11883, tm11883, ep11883, em11883, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11883, agent11883, tp11883, tm11883, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11883, agent11883, scalar11883, tp11883, tm11883, ep11883, em11883, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11883, agent11883, tp11883, tm11883, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11883, agent11883, scalar11883, tp11883, tm11883, ep11883, em11883, dsL]

theorem negative11883 :
    Eminus aL (agent11883.root+dsL) scalar11883.worldRadius world11883.frame
      agent11883.frame tm11883 ≤ -em11883 := by
  apply negative_check (lo := (33582991007635399433 / 50000000000000000000)) (hi := (67165982015270798867 / 100000000000000000000))
    (y := (-((3644564933364340447 / 5000000000000000000)))) (u := (48243311639942789009 / 100000000000000000000))
  · norm_num [world11883, agent11883, scalar11883, tp11883, tm11883, ep11883, em11883, dsL]
  · norm_num [world11883, agent11883, scalar11883, tp11883, tm11883, ep11883, em11883, dsL]
  · norm_num [world11883, agent11883, scalar11883, tp11883, tm11883, ep11883, em11883, dsL]
  · norm_num [world11883, agent11883, scalar11883, tp11883, tm11883, ep11883, em11883, dsL]
  · norm_num [world11883, agent11883, scalar11883, tp11883, tm11883, ep11883, em11883, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11883, agent11883, tp11883, tm11883, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11883, agent11883, tp11883, tm11883, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11883, agent11883, scalar11883, tp11883, tm11883, ep11883, em11883, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11883, agent11883, tp11883, tm11883, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11883, agent11883, scalar11883, tp11883, tm11883, ep11883, em11883, dsL]

theorem tails11883 :
    exp (-((11883:ℝ)*ep11883)) ≤ scalar11883.upperTail ∧
    exp (-((11883:ℝ)*em11883)) ≤ scalar11883.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11883:ℝ)) (by norm_num [ep11883]) ?_)
      (show bp11883^8 ≤ scalar11883.upperTail by norm_num [bp11883, scalar11883])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11883, bp11883, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11883:ℝ)) (by norm_num [em11883]) ?_)
      (show bm11883^8 ≤ scalar11883.lowerTail by norm_num [bm11883, scalar11883])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11883, bm11883, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11883 :
    agent11883.root+dsL+scalar11883.worldRadius < √(1/100/aL) ∧
    2*(agent11883.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11883, agent11883, scalar11883, tp11883, tm11883, ep11883, em11883, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11883, agent11883, scalar11883, tp11883, tm11883, ep11883, em11883, dsL]

noncomputable def master11883 : MasterCertificate 11883 world11883 agent11883 :=
  master scalar11883 dsL tp11883 tm11883 ep11883 em11883
    (by norm_num [dsL]) (by norm_num [tp11883]) (by norm_num [tm11883])
    (by norm_num [ep11883]) (by norm_num [em11883])
    positive11883 negative11883 tails11883.1 tails11883.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11883.1 tailGuards11883.2

theorem preserves11883 : master11883.toScalarCertificate = scalar11883 := rfl

end BstLean.Part281
