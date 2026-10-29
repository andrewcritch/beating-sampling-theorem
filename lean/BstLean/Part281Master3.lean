import BstLean.Part261Checker
import BstLean.Part281Scalar3
namespace BstLean.Part281
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp11934 : ℝ := (604503127 / 2500000000)
noncomputable def tm11934 : ℝ := (-((1250394621 / 2000000000)))
noncomputable def ep11934 : ℝ := (56042566833121679 / 100000000000000000000)
noncomputable def em11934 : ℝ := (13493141848740687 / 25000000000000000000)
noncomputable def bp11934 : ℝ := (43343432626950462101 / 100000000000000000000)
noncomputable def bm11934 : ℝ := (44702722771284754513 / 100000000000000000000)

theorem positive11934 :
    Eplus aL (agent11934.root+dsL) scalar11934.worldRadius world11934.frame
      agent11934.frame tp11934 ≤ -ep11934 := by
  apply positive_check (eT := (116650252923891862193 / 100000000000000000000)) (y := (9937383994584607143 / 25000000000000000000)) (u := (37202322221936119231 / 25000000000000000000))
  · norm_num [world11934, agent11934, scalar11934, tp11934, tm11934, ep11934, em11934, dsL]
  · norm_num [world11934, agent11934, scalar11934, tp11934, tm11934, ep11934, em11934, dsL]
  · norm_num [world11934, agent11934, scalar11934, tp11934, tm11934, ep11934, em11934, dsL]
  · norm_num [world11934, agent11934, scalar11934, tp11934, tm11934, ep11934, em11934, dsL]
  · norm_num [world11934, agent11934, scalar11934, tp11934, tm11934, ep11934, em11934, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11934, agent11934, tp11934, tm11934, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11934, agent11934, scalar11934, tp11934, tm11934, ep11934, em11934, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11934, agent11934, tp11934, tm11934, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11934, agent11934, scalar11934, tp11934, tm11934, ep11934, em11934, dsL]

theorem negative11934 :
    Eminus aL (agent11934.root+dsL) scalar11934.worldRadius world11934.frame
      agent11934.frame tm11934 ≤ -em11934 := by
  apply negative_check (lo := (33576195522637654629 / 50000000000000000000)) (hi := (67152391045275309259 / 100000000000000000000))
    (y := (-((72872739623306568381 / 100000000000000000000)))) (u := (4825226596826073407 / 10000000000000000000))
  · norm_num [world11934, agent11934, scalar11934, tp11934, tm11934, ep11934, em11934, dsL]
  · norm_num [world11934, agent11934, scalar11934, tp11934, tm11934, ep11934, em11934, dsL]
  · norm_num [world11934, agent11934, scalar11934, tp11934, tm11934, ep11934, em11934, dsL]
  · norm_num [world11934, agent11934, scalar11934, tp11934, tm11934, ep11934, em11934, dsL]
  · norm_num [world11934, agent11934, scalar11934, tp11934, tm11934, ep11934, em11934, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11934, agent11934, tp11934, tm11934, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11934, agent11934, tp11934, tm11934, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11934, agent11934, scalar11934, tp11934, tm11934, ep11934, em11934, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11934, agent11934, tp11934, tm11934, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11934, agent11934, scalar11934, tp11934, tm11934, ep11934, em11934, dsL]

theorem tails11934 :
    exp (-((11934:ℝ)*ep11934)) ≤ scalar11934.upperTail ∧
    exp (-((11934:ℝ)*em11934)) ≤ scalar11934.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11934:ℝ)) (by norm_num [ep11934]) ?_)
      (show bp11934^8 ≤ scalar11934.upperTail by norm_num [bp11934, scalar11934])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11934, bp11934, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11934:ℝ)) (by norm_num [em11934]) ?_)
      (show bm11934^8 ≤ scalar11934.lowerTail by norm_num [bm11934, scalar11934])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11934, bm11934, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11934 :
    agent11934.root+dsL+scalar11934.worldRadius < √(1/100/aL) ∧
    2*(agent11934.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11934, agent11934, scalar11934, tp11934, tm11934, ep11934, em11934, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11934, agent11934, scalar11934, tp11934, tm11934, ep11934, em11934, dsL]

noncomputable def master11934 : MasterCertificate 11934 world11934 agent11934 :=
  master scalar11934 dsL tp11934 tm11934 ep11934 em11934
    (by norm_num [dsL]) (by norm_num [tp11934]) (by norm_num [tm11934])
    (by norm_num [ep11934]) (by norm_num [em11934])
    positive11934 negative11934 tails11934.1 tails11934.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11934.1 tailGuards11934.2

theorem preserves11934 : master11934.toScalarCertificate = scalar11934 := rfl

noncomputable def tp11935 : ℝ := (2418109107 / 10000000000)
noncomputable def tm11935 : ℝ := (-((390761727 / 625000000)))
noncomputable def ep11935 : ℝ := (56045413096536151 / 100000000000000000000)
noncomputable def em11935 : ℝ := (26987511842929209 / 50000000000000000000)
noncomputable def bp11935 : ℝ := (5417319509491519641 / 12500000000000000000)
noncomputable def bm11935 : ℝ := (2234903449538317167 / 5000000000000000000)

theorem positive11935 :
    Eplus aL (agent11935.root+dsL) scalar11935.worldRadius world11935.frame
      agent11935.frame tp11935 ≤ -ep11935 := by
  apply positive_check (eT := (58325263516080876111 / 50000000000000000000)) (y := (39750171392453433121 / 100000000000000000000)) (u := (148810234445974609597 / 100000000000000000000))
  · norm_num [world11935, agent11935, scalar11935, tp11935, tm11935, ep11935, em11935, dsL]
  · norm_num [world11935, agent11935, scalar11935, tp11935, tm11935, ep11935, em11935, dsL]
  · norm_num [world11935, agent11935, scalar11935, tp11935, tm11935, ep11935, em11935, dsL]
  · norm_num [world11935, agent11935, scalar11935, tp11935, tm11935, ep11935, em11935, dsL]
  · norm_num [world11935, agent11935, scalar11935, tp11935, tm11935, ep11935, em11935, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11935, agent11935, tp11935, tm11935, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11935, agent11935, scalar11935, tp11935, tm11935, ep11935, em11935, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11935, agent11935, tp11935, tm11935, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11935, agent11935, scalar11935, tp11935, tm11935, ep11935, em11935, dsL]

theorem negative11935 :
    Eminus aL (agent11935.root+dsL) scalar11935.worldRadius world11935.frame
      agent11935.frame tm11935 ≤ -em11935 := by
  apply negative_check (lo := (13430426752458937703 / 20000000000000000000)) (hi := (16788033440573672129 / 25000000000000000000))
    (y := (-((14574472633195986509 / 20000000000000000000)))) (u := (48252447617793155669 / 100000000000000000000))
  · norm_num [world11935, agent11935, scalar11935, tp11935, tm11935, ep11935, em11935, dsL]
  · norm_num [world11935, agent11935, scalar11935, tp11935, tm11935, ep11935, em11935, dsL]
  · norm_num [world11935, agent11935, scalar11935, tp11935, tm11935, ep11935, em11935, dsL]
  · norm_num [world11935, agent11935, scalar11935, tp11935, tm11935, ep11935, em11935, dsL]
  · norm_num [world11935, agent11935, scalar11935, tp11935, tm11935, ep11935, em11935, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11935, agent11935, tp11935, tm11935, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11935, agent11935, tp11935, tm11935, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11935, agent11935, scalar11935, tp11935, tm11935, ep11935, em11935, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11935, agent11935, tp11935, tm11935, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11935, agent11935, scalar11935, tp11935, tm11935, ep11935, em11935, dsL]

theorem tails11935 :
    exp (-((11935:ℝ)*ep11935)) ≤ scalar11935.upperTail ∧
    exp (-((11935:ℝ)*em11935)) ≤ scalar11935.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11935:ℝ)) (by norm_num [ep11935]) ?_)
      (show bp11935^8 ≤ scalar11935.upperTail by norm_num [bp11935, scalar11935])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11935, bp11935, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11935:ℝ)) (by norm_num [em11935]) ?_)
      (show bm11935^8 ≤ scalar11935.lowerTail by norm_num [bm11935, scalar11935])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11935, bm11935, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11935 :
    agent11935.root+dsL+scalar11935.worldRadius < √(1/100/aL) ∧
    2*(agent11935.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11935, agent11935, scalar11935, tp11935, tm11935, ep11935, em11935, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11935, agent11935, scalar11935, tp11935, tm11935, ep11935, em11935, dsL]

noncomputable def master11935 : MasterCertificate 11935 world11935 agent11935 :=
  master scalar11935 dsL tp11935 tm11935 ep11935 em11935
    (by norm_num [dsL]) (by norm_num [tp11935]) (by norm_num [tm11935])
    (by norm_num [ep11935]) (by norm_num [em11935])
    positive11935 negative11935 tails11935.1 tails11935.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11935.1 tailGuards11935.2

theorem preserves11935 : master11935.toScalarCertificate = scalar11935 := rfl

noncomputable def tp11936 : ℝ := (604551419 / 2500000000)
noncomputable def tm11936 : ℝ := (-((1563100581 / 2500000000)))
noncomputable def ep11936 : ℝ := (11209651490036341 / 20000000000000000000)
noncomputable def em11936 : ℝ := (53977478259959211 / 100000000000000000000)
noncomputable def bp11936 : ℝ := (43333680999963999823 / 100000000000000000000)
noncomputable def bm11936 : ℝ := (22346708282541554871 / 50000000000000000000)

theorem positive11936 :
    Eplus aL (agent11936.root+dsL) scalar11936.worldRadius world11936.frame
      agent11936.frame tp11936 ≤ -ep11936 := by
  apply positive_check (eT := (29162700239883425793 / 25000000000000000000)) (y := (9937701670917989011 / 25000000000000000000)) (u := (18601397478416158429 / 12500000000000000000))
  · norm_num [world11936, agent11936, scalar11936, tp11936, tm11936, ep11936, em11936, dsL]
  · norm_num [world11936, agent11936, scalar11936, tp11936, tm11936, ep11936, em11936, dsL]
  · norm_num [world11936, agent11936, scalar11936, tp11936, tm11936, ep11936, em11936, dsL]
  · norm_num [world11936, agent11936, scalar11936, tp11936, tm11936, ep11936, em11936, dsL]
  · norm_num [world11936, agent11936, scalar11936, tp11936, tm11936, ep11936, em11936, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11936, agent11936, tp11936, tm11936, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11936, agent11936, scalar11936, tp11936, tm11936, ep11936, em11936, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11936, agent11936, tp11936, tm11936, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11936, agent11936, scalar11936, tp11936, tm11936, ep11936, em11936, dsL]

theorem negative11936 :
    Eminus aL (agent11936.root+dsL) scalar11936.worldRadius world11936.frame
      agent11936.frame tm11936 ≤ -em11936 := by
  apply negative_check (lo := (33575937852819700277 / 50000000000000000000)) (hi := (13430375141127880111 / 20000000000000000000))
    (y := (-((72871988986137367979 / 100000000000000000000)))) (u := (1507894630283233703 / 3125000000000000000))
  · norm_num [world11936, agent11936, scalar11936, tp11936, tm11936, ep11936, em11936, dsL]
  · norm_num [world11936, agent11936, scalar11936, tp11936, tm11936, ep11936, em11936, dsL]
  · norm_num [world11936, agent11936, scalar11936, tp11936, tm11936, ep11936, em11936, dsL]
  · norm_num [world11936, agent11936, scalar11936, tp11936, tm11936, ep11936, em11936, dsL]
  · norm_num [world11936, agent11936, scalar11936, tp11936, tm11936, ep11936, em11936, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11936, agent11936, tp11936, tm11936, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11936, agent11936, tp11936, tm11936, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11936, agent11936, scalar11936, tp11936, tm11936, ep11936, em11936, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11936, agent11936, tp11936, tm11936, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11936, agent11936, scalar11936, tp11936, tm11936, ep11936, em11936, dsL]

theorem tails11936 :
    exp (-((11936:ℝ)*ep11936)) ≤ scalar11936.upperTail ∧
    exp (-((11936:ℝ)*em11936)) ≤ scalar11936.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11936:ℝ)) (by norm_num [ep11936]) ?_)
      (show bp11936^8 ≤ scalar11936.upperTail by norm_num [bp11936, scalar11936])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11936, bp11936, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11936:ℝ)) (by norm_num [em11936]) ?_)
      (show bm11936^8 ≤ scalar11936.lowerTail by norm_num [bm11936, scalar11936])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11936, bm11936, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11936 :
    agent11936.root+dsL+scalar11936.worldRadius < √(1/100/aL) ∧
    2*(agent11936.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11936, agent11936, scalar11936, tp11936, tm11936, ep11936, em11936, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11936, agent11936, scalar11936, tp11936, tm11936, ep11936, em11936, dsL]

noncomputable def master11936 : MasterCertificate 11936 world11936 agent11936 :=
  master scalar11936 dsL tp11936 tm11936 ep11936 em11936
    (by norm_num [dsL]) (by norm_num [tp11936]) (by norm_num [tm11936])
    (by norm_num [ep11936]) (by norm_num [em11936])
    positive11936 negative11936 tails11936.1 tails11936.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11936.1 tailGuards11936.2

theorem preserves11936 : master11936.toScalarCertificate = scalar11936 := rfl

noncomputable def tp11937 : ℝ := (604575561 / 2500000000)
noncomputable def tm11937 : ℝ := (-((6252616721 / 10000000000)))
noncomputable def ep11937 : ℝ := (5605110001971393 / 10000000000000000000)
noncomputable def em11937 : ℝ := (26989965578012183 / 50000000000000000000)
noncomputable def bp11937 : ℝ := (1733152292709723773 / 4000000000000000000)
noncomputable def bm11937 : ℝ := (44688765468355413363 / 100000000000000000000)

theorem positive11937 :
    Eplus aL (agent11937.root+dsL) scalar11937.worldRadius world11937.frame
      agent11937.frame tp11937 ≤ -ep11937 := by
  apply positive_check (eT := (58325537460726570941 / 50000000000000000000)) (y := (39751442581753032863 / 100000000000000000000)) (u := (148812126117774935397 / 100000000000000000000))
  · norm_num [world11937, agent11937, scalar11937, tp11937, tm11937, ep11937, em11937, dsL]
  · norm_num [world11937, agent11937, scalar11937, tp11937, tm11937, ep11937, em11937, dsL]
  · norm_num [world11937, agent11937, scalar11937, tp11937, tm11937, ep11937, em11937, dsL]
  · norm_num [world11937, agent11937, scalar11937, tp11937, tm11937, ep11937, em11937, dsL]
  · norm_num [world11937, agent11937, scalar11937, tp11937, tm11937, ep11937, em11937, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11937, agent11937, tp11937, tm11937, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11937, agent11937, scalar11937, tp11937, tm11937, ep11937, em11937, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11937, agent11937, tp11937, tm11937, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11937, agent11937, scalar11937, tp11937, tm11937, ep11937, em11937, dsL]

theorem negative11937 :
    Eminus aL (agent11937.root+dsL) scalar11937.worldRadius world11937.frame
      agent11937.frame tm11937 ≤ -em11937 := by
  apply negative_check (lo := (67151618842709360901 / 100000000000000000000)) (hi := (33575809421354680451 / 50000000000000000000))
    (y := (-((3643580644695715229 / 5000000000000000000)))) (u := (4825280964378670199 / 10000000000000000000))
  · norm_num [world11937, agent11937, scalar11937, tp11937, tm11937, ep11937, em11937, dsL]
  · norm_num [world11937, agent11937, scalar11937, tp11937, tm11937, ep11937, em11937, dsL]
  · norm_num [world11937, agent11937, scalar11937, tp11937, tm11937, ep11937, em11937, dsL]
  · norm_num [world11937, agent11937, scalar11937, tp11937, tm11937, ep11937, em11937, dsL]
  · norm_num [world11937, agent11937, scalar11937, tp11937, tm11937, ep11937, em11937, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11937, agent11937, tp11937, tm11937, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11937, agent11937, tp11937, tm11937, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11937, agent11937, scalar11937, tp11937, tm11937, ep11937, em11937, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11937, agent11937, tp11937, tm11937, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11937, agent11937, scalar11937, tp11937, tm11937, ep11937, em11937, dsL]

theorem tails11937 :
    exp (-((11937:ℝ)*ep11937)) ≤ scalar11937.upperTail ∧
    exp (-((11937:ℝ)*em11937)) ≤ scalar11937.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11937:ℝ)) (by norm_num [ep11937]) ?_)
      (show bp11937^8 ≤ scalar11937.upperTail by norm_num [bp11937, scalar11937])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11937, bp11937, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11937:ℝ)) (by norm_num [em11937]) ?_)
      (show bm11937^8 ≤ scalar11937.lowerTail by norm_num [bm11937, scalar11937])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11937, bm11937, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11937 :
    agent11937.root+dsL+scalar11937.worldRadius < √(1/100/aL) ∧
    2*(agent11937.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11937, agent11937, scalar11937, tp11937, tm11937, ep11937, em11937, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11937, agent11937, scalar11937, tp11937, tm11937, ep11937, em11937, dsL]

noncomputable def master11937 : MasterCertificate 11937 world11937 agent11937 :=
  master scalar11937 dsL tp11937 tm11937 ep11937 em11937
    (by norm_num [dsL]) (by norm_num [tp11937]) (by norm_num [tm11937])
    (by norm_num [ep11937]) (by norm_num [em11937])
    positive11937 negative11937 tails11937.1 tails11937.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11937.1 tailGuards11937.2

theorem preserves11937 : master11937.toScalarCertificate = scalar11937 := rfl

noncomputable def tp11938 : ℝ := (2418398733 / 10000000000)
noncomputable def tm11938 : ℝ := (-((390801943 / 625000000)))
noncomputable def ep11938 : ℝ := (28026970947778669 / 50000000000000000000)
noncomputable def em11938 : ℝ := (6747797925934011 / 12500000000000000000)
noncomputable def bp11938 : ℝ := (43323934324251389579 / 100000000000000000000)
noncomputable def bm11938 : ℝ := (11171028752867096757 / 25000000000000000000)

theorem positive11938 :
    Eplus aL (agent11938.root+dsL) scalar11938.worldRadius world11938.frame
      agent11938.frame tp11938 ≤ -ep11938 := by
  apply positive_check (eT := (116651348338430709949 / 100000000000000000000)) (y := (7950415509066346771 / 20000000000000000000)) (u := (74406535511788187263 / 50000000000000000000))
  · norm_num [world11938, agent11938, scalar11938, tp11938, tm11938, ep11938, em11938, dsL]
  · norm_num [world11938, agent11938, scalar11938, tp11938, tm11938, ep11938, em11938, dsL]
  · norm_num [world11938, agent11938, scalar11938, tp11938, tm11938, ep11938, em11938, dsL]
  · norm_num [world11938, agent11938, scalar11938, tp11938, tm11938, ep11938, em11938, dsL]
  · norm_num [world11938, agent11938, scalar11938, tp11938, tm11938, ep11938, em11938, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11938, agent11938, tp11938, tm11938, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11938, agent11938, scalar11938, tp11938, tm11938, ep11938, em11938, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11938, agent11938, tp11938, tm11938, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11938, agent11938, scalar11938, tp11938, tm11938, ep11938, em11938, dsL]

theorem negative11938 :
    Eminus aL (agent11938.root+dsL) scalar11938.worldRadius world11938.frame
      agent11938.frame tm11938 ≤ -em11938 := by
  apply negative_check (lo := (1678784051002979861 / 2500000000000000000)) (hi := (67151362040119194441 / 100000000000000000000))
    (y := (-((18217809445692973831 / 25000000000000000000)))) (u := (24126495322895840247 / 50000000000000000000))
  · norm_num [world11938, agent11938, scalar11938, tp11938, tm11938, ep11938, em11938, dsL]
  · norm_num [world11938, agent11938, scalar11938, tp11938, tm11938, ep11938, em11938, dsL]
  · norm_num [world11938, agent11938, scalar11938, tp11938, tm11938, ep11938, em11938, dsL]
  · norm_num [world11938, agent11938, scalar11938, tp11938, tm11938, ep11938, em11938, dsL]
  · norm_num [world11938, agent11938, scalar11938, tp11938, tm11938, ep11938, em11938, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11938, agent11938, tp11938, tm11938, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11938, agent11938, tp11938, tm11938, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11938, agent11938, scalar11938, tp11938, tm11938, ep11938, em11938, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11938, agent11938, tp11938, tm11938, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11938, agent11938, scalar11938, tp11938, tm11938, ep11938, em11938, dsL]

theorem tails11938 :
    exp (-((11938:ℝ)*ep11938)) ≤ scalar11938.upperTail ∧
    exp (-((11938:ℝ)*em11938)) ≤ scalar11938.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11938:ℝ)) (by norm_num [ep11938]) ?_)
      (show bp11938^8 ≤ scalar11938.upperTail by norm_num [bp11938, scalar11938])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11938, bp11938, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11938:ℝ)) (by norm_num [em11938]) ?_)
      (show bm11938^8 ≤ scalar11938.lowerTail by norm_num [bm11938, scalar11938])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11938, bm11938, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11938 :
    agent11938.root+dsL+scalar11938.worldRadius < √(1/100/aL) ∧
    2*(agent11938.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11938, agent11938, scalar11938, tp11938, tm11938, ep11938, em11938, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11938, agent11938, scalar11938, tp11938, tm11938, ep11938, em11938, dsL]

noncomputable def master11938 : MasterCertificate 11938 world11938 agent11938 :=
  master scalar11938 dsL tp11938 tm11938 ep11938 em11938
    (by norm_num [dsL]) (by norm_num [tp11938]) (by norm_num [tm11938])
    (by norm_num [ep11938]) (by norm_num [em11938])
    positive11938 negative11938 tails11938.1 tails11938.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11938.1 tailGuards11938.2

theorem preserves11938 : master11938.toScalarCertificate = scalar11938 := rfl

noncomputable def tp11939 : ℝ := (2418495159 / 10000000000)
noncomputable def tm11939 : ℝ := (-((3126522651 / 5000000000)))
noncomputable def ep11939 : ℝ := (56056781602918233 / 100000000000000000000)
noncomputable def em11939 : ℝ := (53984833656593069 / 100000000000000000000)
noncomputable def bp11939 : ℝ := (4331906297292133419 / 10000000000000000000)
noncomputable def bm11939 : ℝ := (44679466099731459171 / 100000000000000000000)

theorem positive11939 :
    Eplus aL (agent11939.root+dsL) scalar11939.worldRadius world11939.frame
      agent11939.frame tp11939 ≤ -ep11939 := by
  apply positive_check (eT := (58325810664689215379 / 50000000000000000000)) (y := (39752712014331890083 / 100000000000000000000)) (u := (148814015199375447797 / 100000000000000000000))
  · norm_num [world11939, agent11939, scalar11939, tp11939, tm11939, ep11939, em11939, dsL]
  · norm_num [world11939, agent11939, scalar11939, tp11939, tm11939, ep11939, em11939, dsL]
  · norm_num [world11939, agent11939, scalar11939, tp11939, tm11939, ep11939, em11939, dsL]
  · norm_num [world11939, agent11939, scalar11939, tp11939, tm11939, ep11939, em11939, dsL]
  · norm_num [world11939, agent11939, scalar11939, tp11939, tm11939, ep11939, em11939, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11939, agent11939, tp11939, tm11939, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11939, agent11939, scalar11939, tp11939, tm11939, ep11939, em11939, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11939, agent11939, tp11939, tm11939, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11939, agent11939, scalar11939, tp11939, tm11939, ep11939, em11939, dsL]

theorem negative11939 :
    Eminus aL (agent11939.root+dsL) scalar11939.worldRadius world11939.frame
      agent11939.frame tm11939 ≤ -em11939 := by
  apply negative_check (lo := (67151105823858182417 / 100000000000000000000)) (hi := (33575552911929091209 / 50000000000000000000))
    (y := (-((72870862101587295487 / 100000000000000000000)))) (u := (24126585961769528217 / 50000000000000000000))
  · norm_num [world11939, agent11939, scalar11939, tp11939, tm11939, ep11939, em11939, dsL]
  · norm_num [world11939, agent11939, scalar11939, tp11939, tm11939, ep11939, em11939, dsL]
  · norm_num [world11939, agent11939, scalar11939, tp11939, tm11939, ep11939, em11939, dsL]
  · norm_num [world11939, agent11939, scalar11939, tp11939, tm11939, ep11939, em11939, dsL]
  · norm_num [world11939, agent11939, scalar11939, tp11939, tm11939, ep11939, em11939, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11939, agent11939, tp11939, tm11939, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11939, agent11939, tp11939, tm11939, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11939, agent11939, scalar11939, tp11939, tm11939, ep11939, em11939, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11939, agent11939, tp11939, tm11939, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11939, agent11939, scalar11939, tp11939, tm11939, ep11939, em11939, dsL]

theorem tails11939 :
    exp (-((11939:ℝ)*ep11939)) ≤ scalar11939.upperTail ∧
    exp (-((11939:ℝ)*em11939)) ≤ scalar11939.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11939:ℝ)) (by norm_num [ep11939]) ?_)
      (show bp11939^8 ≤ scalar11939.upperTail by norm_num [bp11939, scalar11939])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11939, bp11939, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11939:ℝ)) (by norm_num [em11939]) ?_)
      (show bm11939^8 ≤ scalar11939.lowerTail by norm_num [bm11939, scalar11939])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11939, bm11939, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11939 :
    agent11939.root+dsL+scalar11939.worldRadius < √(1/100/aL) ∧
    2*(agent11939.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11939, agent11939, scalar11939, tp11939, tm11939, ep11939, em11939, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11939, agent11939, scalar11939, tp11939, tm11939, ep11939, em11939, dsL]

noncomputable def master11939 : MasterCertificate 11939 world11939 agent11939 :=
  master scalar11939 dsL tp11939 tm11939 ep11939 em11939
    (by norm_num [dsL]) (by norm_num [tp11939]) (by norm_num [tm11939])
    (by norm_num [ep11939]) (by norm_num [em11939])
    positive11939 negative11939 tails11939.1 tails11939.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11939.1 tailGuards11939.2

theorem preserves11939 : master11939.toScalarCertificate = scalar11939 := rfl

noncomputable def tp11940 : ℝ := (2418591519 / 10000000000)
noncomputable def tm11940 : ℝ := (-((390828707 / 625000000)))
noncomputable def ep11940 : ℝ := (56059619635188277 / 100000000000000000000)
noncomputable def em11940 : ℝ := (13496820589387973 / 25000000000000000000)
noncomputable def bp11940 : ℝ := (21657096472357167579 / 50000000000000000000)
noncomputable def bm11940 : ℝ := (44674818430274421229 / 100000000000000000000)

theorem positive11940 :
    Eplus aL (agent11940.root+dsL) scalar11940.worldRadius world11940.frame
      agent11940.frame tp11940 ≤ -ep11940 := by
  apply positive_check (eT := (11665189387199435511 / 10000000000000000000)) (y := (2484584117699846861 / 6250000000000000000)) (u := (148814958488075138253 / 100000000000000000000))
  · norm_num [world11940, agent11940, scalar11940, tp11940, tm11940, ep11940, em11940, dsL]
  · norm_num [world11940, agent11940, scalar11940, tp11940, tm11940, ep11940, em11940, dsL]
  · norm_num [world11940, agent11940, scalar11940, tp11940, tm11940, ep11940, em11940, dsL]
  · norm_num [world11940, agent11940, scalar11940, tp11940, tm11940, ep11940, em11940, dsL]
  · norm_num [world11940, agent11940, scalar11940, tp11940, tm11940, ep11940, em11940, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11940, agent11940, tp11940, tm11940, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11940, agent11940, scalar11940, tp11940, tm11940, ep11940, em11940, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11940, agent11940, tp11940, tm11940, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11940, agent11940, scalar11940, tp11940, tm11940, ep11940, em11940, dsL]

theorem negative11940 :
    Eminus aL (agent11940.root+dsL) scalar11940.worldRadius world11940.frame
      agent11940.frame tm11940 ≤ -em11940 := by
  apply negative_check (lo := (67150850412039425917 / 100000000000000000000)) (hi := (33575425206019712959 / 50000000000000000000))
    (y := (-((36435242747019185901 / 50000000000000000000)))) (u := (9650670729793862247 / 20000000000000000000))
  · norm_num [world11940, agent11940, scalar11940, tp11940, tm11940, ep11940, em11940, dsL]
  · norm_num [world11940, agent11940, scalar11940, tp11940, tm11940, ep11940, em11940, dsL]
  · norm_num [world11940, agent11940, scalar11940, tp11940, tm11940, ep11940, em11940, dsL]
  · norm_num [world11940, agent11940, scalar11940, tp11940, tm11940, ep11940, em11940, dsL]
  · norm_num [world11940, agent11940, scalar11940, tp11940, tm11940, ep11940, em11940, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11940, agent11940, tp11940, tm11940, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11940, agent11940, tp11940, tm11940, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11940, agent11940, scalar11940, tp11940, tm11940, ep11940, em11940, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11940, agent11940, tp11940, tm11940, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11940, agent11940, scalar11940, tp11940, tm11940, ep11940, em11940, dsL]

theorem tails11940 :
    exp (-((11940:ℝ)*ep11940)) ≤ scalar11940.upperTail ∧
    exp (-((11940:ℝ)*em11940)) ≤ scalar11940.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11940:ℝ)) (by norm_num [ep11940]) ?_)
      (show bp11940^8 ≤ scalar11940.upperTail by norm_num [bp11940, scalar11940])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11940, bp11940, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11940:ℝ)) (by norm_num [em11940]) ?_)
      (show bm11940^8 ≤ scalar11940.lowerTail by norm_num [bm11940, scalar11940])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11940, bm11940, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11940 :
    agent11940.root+dsL+scalar11940.worldRadius < √(1/100/aL) ∧
    2*(agent11940.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11940, agent11940, scalar11940, tp11940, tm11940, ep11940, em11940, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11940, agent11940, scalar11940, tp11940, tm11940, ep11940, em11940, dsL]

noncomputable def master11940 : MasterCertificate 11940 world11940 agent11940 :=
  master scalar11940 dsL tp11940 tm11940 ep11940 em11940
    (by norm_num [dsL]) (by norm_num [tp11940]) (by norm_num [tm11940])
    (by norm_num [ep11940]) (by norm_num [em11940])
    positive11940 negative11940 tails11940.1 tails11940.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11940.1 tailGuards11940.2

theorem preserves11940 : master11940.toScalarCertificate = scalar11940 := rfl

noncomputable def tp11941 : ℝ := (2418687889 / 10000000000)
noncomputable def tm11941 : ℝ := (-((195421043 / 312500000)))
noncomputable def ep11941 : ℝ := (56062456147600447 / 100000000000000000000)
noncomputable def em11941 : ℝ := (3374358104443719 / 6250000000000000000)
noncomputable def bp11941 : ℝ := (21654662069614818961 / 50000000000000000000)
noncomputable def bm11941 : ℝ := (5583771486985943481 / 12500000000000000000)

theorem positive11941 :
    Eplus aL (agent11941.root+dsL) scalar11941.worldRadius world11941.frame
      agent11941.frame tp11941 ≤ -ep11941 := by
  apply positive_check (eT := (4666086661236963023 / 4000000000000000000)) (y := (795079606774024807 / 2000000000000000000)) (u := (148815902655764739457 / 100000000000000000000))
  · norm_num [world11941, agent11941, scalar11941, tp11941, tm11941, ep11941, em11941, dsL]
  · norm_num [world11941, agent11941, scalar11941, tp11941, tm11941, ep11941, em11941, dsL]
  · norm_num [world11941, agent11941, scalar11941, tp11941, tm11941, ep11941, em11941, dsL]
  · norm_num [world11941, agent11941, scalar11941, tp11941, tm11941, ep11941, em11941, dsL]
  · norm_num [world11941, agent11941, scalar11941, tp11941, tm11941, ep11941, em11941, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11941, agent11941, tp11941, tm11941, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11941, agent11941, scalar11941, tp11941, tm11941, ep11941, em11941, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11941, agent11941, tp11941, tm11941, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11941, agent11941, scalar11941, tp11941, tm11941, ep11941, em11941, dsL]

theorem negative11941 :
    Eminus aL (agent11941.root+dsL) scalar11941.worldRadius world11941.frame
      agent11941.frame tm11941 ≤ -em11941 := by
  apply negative_check (lo := (33575297350628851427 / 50000000000000000000)) (hi := (13430118940251540571 / 20000000000000000000))
    (y := (-((14574022022463482111 / 20000000000000000000)))) (u := (48253534783578633147 / 100000000000000000000))
  · norm_num [world11941, agent11941, scalar11941, tp11941, tm11941, ep11941, em11941, dsL]
  · norm_num [world11941, agent11941, scalar11941, tp11941, tm11941, ep11941, em11941, dsL]
  · norm_num [world11941, agent11941, scalar11941, tp11941, tm11941, ep11941, em11941, dsL]
  · norm_num [world11941, agent11941, scalar11941, tp11941, tm11941, ep11941, em11941, dsL]
  · norm_num [world11941, agent11941, scalar11941, tp11941, tm11941, ep11941, em11941, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11941, agent11941, tp11941, tm11941, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11941, agent11941, tp11941, tm11941, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11941, agent11941, scalar11941, tp11941, tm11941, ep11941, em11941, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11941, agent11941, tp11941, tm11941, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11941, agent11941, scalar11941, tp11941, tm11941, ep11941, em11941, dsL]

theorem tails11941 :
    exp (-((11941:ℝ)*ep11941)) ≤ scalar11941.upperTail ∧
    exp (-((11941:ℝ)*em11941)) ≤ scalar11941.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11941:ℝ)) (by norm_num [ep11941]) ?_)
      (show bp11941^8 ≤ scalar11941.upperTail by norm_num [bp11941, scalar11941])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11941, bp11941, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11941:ℝ)) (by norm_num [em11941]) ?_)
      (show bm11941^8 ≤ scalar11941.lowerTail by norm_num [bm11941, scalar11941])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11941, bm11941, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11941 :
    agent11941.root+dsL+scalar11941.worldRadius < √(1/100/aL) ∧
    2*(agent11941.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11941, agent11941, scalar11941, tp11941, tm11941, ep11941, em11941, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11941, agent11941, scalar11941, tp11941, tm11941, ep11941, em11941, dsL]

noncomputable def master11941 : MasterCertificate 11941 world11941 agent11941 :=
  master scalar11941 dsL tp11941 tm11941 ep11941 em11941
    (by norm_num [dsL]) (by norm_num [tp11941]) (by norm_num [tm11941])
    (by norm_num [ep11941]) (by norm_num [em11941])
    positive11941 negative11941 tails11941.1 tails11941.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11941.1 tailGuards11941.2

theorem preserves11941 : master11941.toScalarCertificate = scalar11941 := rfl

noncomputable def tp11942 : ℝ := (2418784171 / 10000000000)
noncomputable def tm11942 : ℝ := (-((3126843557 / 5000000000)))
noncomputable def ep11942 : ℝ := (56065290829871197 / 100000000000000000000)
noncomputable def em11942 : ℝ := (26996087638029539 / 50000000000000000000)
noncomputable def bp11942 : ℝ := (5413057094625069083 / 12500000000000000000)
noncomputable def bm11942 : ℝ := (8933105342138509393 / 20000000000000000000)

theorem positive11942 :
    Eplus aL (agent11942.root+dsL) scalar11942.worldRadius world11942.frame
      agent11942.frame tp11942 ≤ -ep11942 := by
  apply positive_check (eT := (4666097543125088413 / 4000000000000000000)) (y := (9938653491081866393 / 25000000000000000000)) (u := (74408422797223606087 / 50000000000000000000))
  · norm_num [world11942, agent11942, scalar11942, tp11942, tm11942, ep11942, em11942, dsL]
  · norm_num [world11942, agent11942, scalar11942, tp11942, tm11942, ep11942, em11942, dsL]
  · norm_num [world11942, agent11942, scalar11942, tp11942, tm11942, ep11942, em11942, dsL]
  · norm_num [world11942, agent11942, scalar11942, tp11942, tm11942, ep11942, em11942, dsL]
  · norm_num [world11942, agent11942, scalar11942, tp11942, tm11942, ep11942, em11942, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11942, agent11942, tp11942, tm11942, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11942, agent11942, scalar11942, tp11942, tm11942, ep11942, em11942, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11942, agent11942, tp11942, tm11942, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11942, agent11942, scalar11942, tp11942, tm11942, ep11942, em11942, dsL]

theorem negative11942 :
    Eminus aL (agent11942.root+dsL) scalar11942.worldRadius world11942.frame
      agent11942.frame tm11942 ≤ -em11942 := by
  apply negative_check (lo := (67150340316542274563 / 100000000000000000000)) (hi := (16787585079135568641 / 25000000000000000000))
    (y := (-((18217433235245591703 / 25000000000000000000)))) (u := (6031714597802900711 / 12500000000000000000))
  · norm_num [world11942, agent11942, scalar11942, tp11942, tm11942, ep11942, em11942, dsL]
  · norm_num [world11942, agent11942, scalar11942, tp11942, tm11942, ep11942, em11942, dsL]
  · norm_num [world11942, agent11942, scalar11942, tp11942, tm11942, ep11942, em11942, dsL]
  · norm_num [world11942, agent11942, scalar11942, tp11942, tm11942, ep11942, em11942, dsL]
  · norm_num [world11942, agent11942, scalar11942, tp11942, tm11942, ep11942, em11942, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11942, agent11942, tp11942, tm11942, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11942, agent11942, tp11942, tm11942, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11942, agent11942, scalar11942, tp11942, tm11942, ep11942, em11942, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11942, agent11942, tp11942, tm11942, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11942, agent11942, scalar11942, tp11942, tm11942, ep11942, em11942, dsL]

theorem tails11942 :
    exp (-((11942:ℝ)*ep11942)) ≤ scalar11942.upperTail ∧
    exp (-((11942:ℝ)*em11942)) ≤ scalar11942.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11942:ℝ)) (by norm_num [ep11942]) ?_)
      (show bp11942^8 ≤ scalar11942.upperTail by norm_num [bp11942, scalar11942])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11942, bp11942, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11942:ℝ)) (by norm_num [em11942]) ?_)
      (show bm11942^8 ≤ scalar11942.lowerTail by norm_num [bm11942, scalar11942])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11942, bm11942, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11942 :
    agent11942.root+dsL+scalar11942.worldRadius < √(1/100/aL) ∧
    2*(agent11942.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11942, agent11942, scalar11942, tp11942, tm11942, ep11942, em11942, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11942, agent11942, scalar11942, tp11942, tm11942, ep11942, em11942, dsL]

noncomputable def master11942 : MasterCertificate 11942 world11942 agent11942 :=
  master scalar11942 dsL tp11942 tm11942 ep11942 em11942
    (by norm_num [dsL]) (by norm_num [tp11942]) (by norm_num [tm11942])
    (by norm_num [ep11942]) (by norm_num [em11942])
    positive11942 negative11942 tails11942.1 tails11942.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11942.1 tailGuards11942.2

theorem preserves11942 : master11942.toScalarCertificate = scalar11942 := rfl

noncomputable def tp11943 : ℝ := (2418880411 / 10000000000)
noncomputable def tm11943 : ℝ := (-((6253900743 / 10000000000)))
noncomputable def ep11943 : ℝ := (56068123842198533 / 100000000000000000000)
noncomputable def em11943 : ℝ := (26997309668689031 / 50000000000000000000)
noncomputable def bp11943 : ℝ := (43299590694413990579 / 100000000000000000000)
noncomputable def bm11943 : ℝ := (22330441382339783601 / 50000000000000000000)

theorem positive11943 :
    Eplus aL (agent11943.root+dsL) scalar11943.worldRadius world11943.frame
      agent11943.frame tp11943 ≤ -ep11943 := by
  apply positive_check (eT := (23330542071066002447 / 20000000000000000000)) (y := (3975524741476480661 / 10000000000000000000)) (u := (148817788278392181971 / 100000000000000000000))
  · norm_num [world11943, agent11943, scalar11943, tp11943, tm11943, ep11943, em11943, dsL]
  · norm_num [world11943, agent11943, scalar11943, tp11943, tm11943, ep11943, em11943, dsL]
  · norm_num [world11943, agent11943, scalar11943, tp11943, tm11943, ep11943, em11943, dsL]
  · norm_num [world11943, agent11943, scalar11943, tp11943, tm11943, ep11943, em11943, dsL]
  · norm_num [world11943, agent11943, scalar11943, tp11943, tm11943, ep11943, em11943, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11943, agent11943, tp11943, tm11943, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11943, agent11943, scalar11943, tp11943, tm11943, ep11943, em11943, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11943, agent11943, tp11943, tm11943, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11943, agent11943, scalar11943, tp11943, tm11943, ep11943, em11943, dsL]

theorem negative11943 :
    Eminus aL (agent11943.root+dsL) scalar11943.worldRadius world11943.frame
      agent11943.frame tm11943 ≤ -em11943 := by
  apply negative_check (lo := (33575043164953669361 / 50000000000000000000)) (hi := (67150086329907338723 / 100000000000000000000))
    (y := (-((36434677871635880567 / 50000000000000000000)))) (u := (12063474698670365989 / 25000000000000000000))
  · norm_num [world11943, agent11943, scalar11943, tp11943, tm11943, ep11943, em11943, dsL]
  · norm_num [world11943, agent11943, scalar11943, tp11943, tm11943, ep11943, em11943, dsL]
  · norm_num [world11943, agent11943, scalar11943, tp11943, tm11943, ep11943, em11943, dsL]
  · norm_num [world11943, agent11943, scalar11943, tp11943, tm11943, ep11943, em11943, dsL]
  · norm_num [world11943, agent11943, scalar11943, tp11943, tm11943, ep11943, em11943, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11943, agent11943, tp11943, tm11943, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11943, agent11943, tp11943, tm11943, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11943, agent11943, scalar11943, tp11943, tm11943, ep11943, em11943, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11943, agent11943, tp11943, tm11943, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11943, agent11943, scalar11943, tp11943, tm11943, ep11943, em11943, dsL]

theorem tails11943 :
    exp (-((11943:ℝ)*ep11943)) ≤ scalar11943.upperTail ∧
    exp (-((11943:ℝ)*em11943)) ≤ scalar11943.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11943:ℝ)) (by norm_num [ep11943]) ?_)
      (show bp11943^8 ≤ scalar11943.upperTail by norm_num [bp11943, scalar11943])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11943, bp11943, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11943:ℝ)) (by norm_num [em11943]) ?_)
      (show bm11943^8 ≤ scalar11943.lowerTail by norm_num [bm11943, scalar11943])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11943, bm11943, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11943 :
    agent11943.root+dsL+scalar11943.worldRadius < √(1/100/aL) ∧
    2*(agent11943.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11943, agent11943, scalar11943, tp11943, tm11943, ep11943, em11943, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11943, agent11943, scalar11943, tp11943, tm11943, ep11943, em11943, dsL]

noncomputable def master11943 : MasterCertificate 11943 world11943 agent11943 :=
  master scalar11943 dsL tp11943 tm11943 ep11943 em11943
    (by norm_num [dsL]) (by norm_num [tp11943]) (by norm_num [tm11943])
    (by norm_num [ep11943]) (by norm_num [em11943])
    positive11943 negative11943 tails11943.1 tails11943.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11943.1 tailGuards11943.2

theorem preserves11943 : master11943.toScalarCertificate = scalar11943 := rfl

noncomputable def tp11944 : ℝ := (2418976611 / 10000000000)
noncomputable def tm11944 : ℝ := (-((97720539 / 156250000)))
noncomputable def ep11944 : ℝ := (56070955334986219 / 100000000000000000000)
noncomputable def em11944 : ℝ := (3374816375733193 / 6250000000000000000)
noncomputable def bp11944 : ℝ := (676480091471869007 / 1562500000000000000)
noncomputable def bm11944 : ℝ := (22328119976681641103 / 50000000000000000000)

theorem positive11944 :
    Eplus aL (agent11944.root+dsL) scalar11944.worldRadius world11944.frame
      agent11944.frame tp11944 ≤ -ep11944 := by
  apply positive_check (eT := (116652981877419065191 / 100000000000000000000)) (y := (7951176112877282727 / 20000000000000000000)) (u := (18602341315079806127 / 12500000000000000000))
  · norm_num [world11944, agent11944, scalar11944, tp11944, tm11944, ep11944, em11944, dsL]
  · norm_num [world11944, agent11944, scalar11944, tp11944, tm11944, ep11944, em11944, dsL]
  · norm_num [world11944, agent11944, scalar11944, tp11944, tm11944, ep11944, em11944, dsL]
  · norm_num [world11944, agent11944, scalar11944, tp11944, tm11944, ep11944, em11944, dsL]
  · norm_num [world11944, agent11944, scalar11944, tp11944, tm11944, ep11944, em11944, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11944, agent11944, tp11944, tm11944, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11944, agent11944, scalar11944, tp11944, tm11944, ep11944, em11944, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11944, agent11944, tp11944, tm11944, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11944, agent11944, scalar11944, tp11944, tm11944, ep11944, em11944, dsL]

theorem negative11944 :
    Eminus aL (agent11944.root+dsL) scalar11944.worldRadius world11944.frame
      agent11944.frame tm11944 ≤ -em11944 := by
  apply negative_check (lo := (67149831745016242849 / 100000000000000000000)) (hi := (1342996634900324857 / 2000000000000000000))
    (y := (-((72868980433835156541 / 100000000000000000000)))) (u := (48254079896457015839 / 100000000000000000000))
  · norm_num [world11944, agent11944, scalar11944, tp11944, tm11944, ep11944, em11944, dsL]
  · norm_num [world11944, agent11944, scalar11944, tp11944, tm11944, ep11944, em11944, dsL]
  · norm_num [world11944, agent11944, scalar11944, tp11944, tm11944, ep11944, em11944, dsL]
  · norm_num [world11944, agent11944, scalar11944, tp11944, tm11944, ep11944, em11944, dsL]
  · norm_num [world11944, agent11944, scalar11944, tp11944, tm11944, ep11944, em11944, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11944, agent11944, tp11944, tm11944, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11944, agent11944, tp11944, tm11944, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11944, agent11944, scalar11944, tp11944, tm11944, ep11944, em11944, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11944, agent11944, tp11944, tm11944, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11944, agent11944, scalar11944, tp11944, tm11944, ep11944, em11944, dsL]

theorem tails11944 :
    exp (-((11944:ℝ)*ep11944)) ≤ scalar11944.upperTail ∧
    exp (-((11944:ℝ)*em11944)) ≤ scalar11944.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11944:ℝ)) (by norm_num [ep11944]) ?_)
      (show bp11944^8 ≤ scalar11944.upperTail by norm_num [bp11944, scalar11944])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11944, bp11944, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11944:ℝ)) (by norm_num [em11944]) ?_)
      (show bm11944^8 ≤ scalar11944.lowerTail by norm_num [bm11944, scalar11944])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11944, bm11944, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11944 :
    agent11944.root+dsL+scalar11944.worldRadius < √(1/100/aL) ∧
    2*(agent11944.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11944, agent11944, scalar11944, tp11944, tm11944, ep11944, em11944, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11944, agent11944, scalar11944, tp11944, tm11944, ep11944, em11944, dsL]

noncomputable def master11944 : MasterCertificate 11944 world11944 agent11944 :=
  master scalar11944 dsL tp11944 tm11944 ep11944 em11944
    (by norm_num [dsL]) (by norm_num [tp11944]) (by norm_num [tm11944])
    (by norm_num [ep11944]) (by norm_num [em11944])
    positive11944 negative11944 tails11944.1 tails11944.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11944.1 tailGuards11944.2

theorem preserves11944 : master11944.toScalarCertificate = scalar11944 := rfl

noncomputable def tp11945 : ℝ := (604768177 / 2500000000)
noncomputable def tm11945 : ℝ := (-((1563581957 / 2500000000)))
noncomputable def ep11945 : ℝ := (56073785002771187 / 100000000000000000000)
noncomputable def em11945 : ℝ := (6749937872751237 / 12500000000000000000)
noncomputable def bp11945 : ℝ := (43289862433757655179 / 100000000000000000000)
noncomputable def bm11945 : ℝ := (44651598488139835173 / 100000000000000000000)

theorem positive11945 :
    Eplus aL (agent11945.root+dsL) scalar11945.worldRadius world11945.frame
      agent11945.frame tp11945 ≤ -ep11945 := by
  apply positive_check (eT := (11665325267643427757 / 10000000000000000000)) (y := (9939128154379492779 / 25000000000000000000)) (u := (29763934227411528687 / 20000000000000000000))
  · norm_num [world11945, agent11945, scalar11945, tp11945, tm11945, ep11945, em11945, dsL]
  · norm_num [world11945, agent11945, scalar11945, tp11945, tm11945, ep11945, em11945, dsL]
  · norm_num [world11945, agent11945, scalar11945, tp11945, tm11945, ep11945, em11945, dsL]
  · norm_num [world11945, agent11945, scalar11945, tp11945, tm11945, ep11945, em11945, dsL]
  · norm_num [world11945, agent11945, scalar11945, tp11945, tm11945, ep11945, em11945, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11945, agent11945, tp11945, tm11945, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11945, agent11945, scalar11945, tp11945, tm11945, ep11945, em11945, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11945, agent11945, tp11945, tm11945, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11945, agent11945, scalar11945, tp11945, tm11945, ep11945, em11945, dsL]

theorem negative11945 :
    Eminus aL (agent11945.root+dsL) scalar11945.worldRadius world11945.frame
      agent11945.frame tm11945 ≤ -em11945 := by
  apply negative_check (lo := (67149578892247507759 / 100000000000000000000)) (hi := (839369736153093847 / 1250000000000000000))
    (y := (-((72868602432626415477 / 100000000000000000000)))) (u := (24127131148903515381 / 50000000000000000000))
  · norm_num [world11945, agent11945, scalar11945, tp11945, tm11945, ep11945, em11945, dsL]
  · norm_num [world11945, agent11945, scalar11945, tp11945, tm11945, ep11945, em11945, dsL]
  · norm_num [world11945, agent11945, scalar11945, tp11945, tm11945, ep11945, em11945, dsL]
  · norm_num [world11945, agent11945, scalar11945, tp11945, tm11945, ep11945, em11945, dsL]
  · norm_num [world11945, agent11945, scalar11945, tp11945, tm11945, ep11945, em11945, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11945, agent11945, tp11945, tm11945, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11945, agent11945, tp11945, tm11945, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11945, agent11945, scalar11945, tp11945, tm11945, ep11945, em11945, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11945, agent11945, tp11945, tm11945, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11945, agent11945, scalar11945, tp11945, tm11945, ep11945, em11945, dsL]

theorem tails11945 :
    exp (-((11945:ℝ)*ep11945)) ≤ scalar11945.upperTail ∧
    exp (-((11945:ℝ)*em11945)) ≤ scalar11945.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11945:ℝ)) (by norm_num [ep11945]) ?_)
      (show bp11945^8 ≤ scalar11945.upperTail by norm_num [bp11945, scalar11945])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11945, bp11945, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11945:ℝ)) (by norm_num [em11945]) ?_)
      (show bm11945^8 ≤ scalar11945.lowerTail by norm_num [bm11945, scalar11945])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11945, bm11945, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11945 :
    agent11945.root+dsL+scalar11945.worldRadius < √(1/100/aL) ∧
    2*(agent11945.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11945, agent11945, scalar11945, tp11945, tm11945, ep11945, em11945, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11945, agent11945, scalar11945, tp11945, tm11945, ep11945, em11945, dsL]

noncomputable def master11945 : MasterCertificate 11945 world11945 agent11945 :=
  master scalar11945 dsL tp11945 tm11945 ep11945 em11945
    (by norm_num [dsL]) (by norm_num [tp11945]) (by norm_num [tm11945])
    (by norm_num [ep11945]) (by norm_num [em11945])
    positive11945 negative11945 tails11945.1 tails11945.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11945.1 tailGuards11945.2

theorem preserves11945 : master11945.toScalarCertificate = scalar11945 := rfl

noncomputable def tp11946 : ℝ := (2419168789 / 10000000000)
noncomputable def tm11946 : ℝ := (-((6254541193 / 10000000000)))
noncomputable def ep11946 : ℝ := (56076612657778451 / 100000000000000000000)
noncomputable def em11946 : ℝ := (10800388422286983 / 20000000000000000000)
noncomputable def bp11946 : ℝ := (10821250138599410127 / 25000000000000000000)
noncomputable def bm11946 : ℝ := (11161739615041198613 / 25000000000000000000)

theorem positive11946 :
    Eplus aL (agent11946.root+dsL) scalar11946.worldRadius world11946.frame
      agent11946.frame tp11946 ≤ -ep11946 := by
  apply positive_check (eT := (116653523398654047267 / 100000000000000000000)) (y := (39757144847101001727 / 100000000000000000000)) (u := (148820612022018214179 / 100000000000000000000))
  · norm_num [world11946, agent11946, scalar11946, tp11946, tm11946, ep11946, em11946, dsL]
  · norm_num [world11946, agent11946, scalar11946, tp11946, tm11946, ep11946, em11946, dsL]
  · norm_num [world11946, agent11946, scalar11946, tp11946, tm11946, ep11946, em11946, dsL]
  · norm_num [world11946, agent11946, scalar11946, tp11946, tm11946, ep11946, em11946, dsL]
  · norm_num [world11946, agent11946, scalar11946, tp11946, tm11946, ep11946, em11946, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11946, agent11946, tp11946, tm11946, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11946, agent11946, scalar11946, tp11946, tm11946, ep11946, em11946, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11946, agent11946, tp11946, tm11946, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11946, agent11946, scalar11946, tp11946, tm11946, ep11946, em11946, dsL]

theorem negative11946 :
    Eminus aL (agent11946.root+dsL) scalar11946.worldRadius world11946.frame
      agent11946.frame tm11946 ≤ -em11946 := by
  apply negative_check (lo := (67149325830286011409 / 100000000000000000000)) (hi := (6714932583028601141 / 10000000000000000000))
    (y := (-((18217056331924957411 / 25000000000000000000)))) (u := (12063611066837637821 / 25000000000000000000))
  · norm_num [world11946, agent11946, scalar11946, tp11946, tm11946, ep11946, em11946, dsL]
  · norm_num [world11946, agent11946, scalar11946, tp11946, tm11946, ep11946, em11946, dsL]
  · norm_num [world11946, agent11946, scalar11946, tp11946, tm11946, ep11946, em11946, dsL]
  · norm_num [world11946, agent11946, scalar11946, tp11946, tm11946, ep11946, em11946, dsL]
  · norm_num [world11946, agent11946, scalar11946, tp11946, tm11946, ep11946, em11946, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11946, agent11946, tp11946, tm11946, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11946, agent11946, tp11946, tm11946, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11946, agent11946, scalar11946, tp11946, tm11946, ep11946, em11946, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11946, agent11946, tp11946, tm11946, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11946, agent11946, scalar11946, tp11946, tm11946, ep11946, em11946, dsL]

theorem tails11946 :
    exp (-((11946:ℝ)*ep11946)) ≤ scalar11946.upperTail ∧
    exp (-((11946:ℝ)*em11946)) ≤ scalar11946.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11946:ℝ)) (by norm_num [ep11946]) ?_)
      (show bp11946^8 ≤ scalar11946.upperTail by norm_num [bp11946, scalar11946])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11946, bp11946, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11946:ℝ)) (by norm_num [em11946]) ?_)
      (show bm11946^8 ≤ scalar11946.lowerTail by norm_num [bm11946, scalar11946])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11946, bm11946, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11946 :
    agent11946.root+dsL+scalar11946.worldRadius < √(1/100/aL) ∧
    2*(agent11946.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11946, agent11946, scalar11946, tp11946, tm11946, ep11946, em11946, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11946, agent11946, scalar11946, tp11946, tm11946, ep11946, em11946, dsL]

noncomputable def master11946 : MasterCertificate 11946 world11946 agent11946 :=
  master scalar11946 dsL tp11946 tm11946 ep11946 em11946
    (by norm_num [dsL]) (by norm_num [tp11946]) (by norm_num [tm11946])
    (by norm_num [ep11946]) (by norm_num [em11946])
    positive11946 negative11946 tails11946.1 tails11946.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11946.1 tailGuards11946.2

theorem preserves11946 : master11946.toScalarCertificate = scalar11946 := rfl

noncomputable def tp11947 : ℝ := (483852957 / 2000000000)
noncomputable def tm11947 : ℝ := (-((6254754479 / 10000000000)))
noncomputable def ep11947 : ℝ := (28039719625086543 / 50000000000000000000)
noncomputable def em11947 : ℝ := (6750547535684183 / 12500000000000000000)
noncomputable def bp11947 : ℝ := (43280139601924969653 / 100000000000000000000)
noncomputable def bm11947 : ℝ := (348768119367793899 / 781250000000000000)

theorem positive11947 :
    Eplus aL (agent11947.root+dsL) scalar11947.worldRadius world11947.frame
      agent11947.frame tp11947 ≤ -ep11947 := by
  apply positive_check (eT := (5832689676576662763 / 5000000000000000000)) (y := (993944400814176659 / 2500000000000000000)) (u := (74410775679528140953 / 50000000000000000000))
  · norm_num [world11947, agent11947, scalar11947, tp11947, tm11947, ep11947, em11947, dsL]
  · norm_num [world11947, agent11947, scalar11947, tp11947, tm11947, ep11947, em11947, dsL]
  · norm_num [world11947, agent11947, scalar11947, tp11947, tm11947, ep11947, em11947, dsL]
  · norm_num [world11947, agent11947, scalar11947, tp11947, tm11947, ep11947, em11947, dsL]
  · norm_num [world11947, agent11947, scalar11947, tp11947, tm11947, ep11947, em11947, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11947, agent11947, tp11947, tm11947, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11947, agent11947, scalar11947, tp11947, tm11947, ep11947, em11947, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11947, agent11947, tp11947, tm11947, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11947, agent11947, scalar11947, tp11947, tm11947, ep11947, em11947, dsL]

theorem negative11947 :
    Eminus aL (agent11947.root+dsL) scalar11947.worldRadius world11947.frame
      agent11947.frame tm11947 ≤ -em11947 := by
  apply negative_check (lo := (13429814607615494171 / 20000000000000000000)) (hi := (8393634129759683857 / 12500000000000000000))
    (y := (-((2277120272839450903 / 3125000000000000000)))) (u := (2412731299620187631 / 5000000000000000000))
  · norm_num [world11947, agent11947, scalar11947, tp11947, tm11947, ep11947, em11947, dsL]
  · norm_num [world11947, agent11947, scalar11947, tp11947, tm11947, ep11947, em11947, dsL]
  · norm_num [world11947, agent11947, scalar11947, tp11947, tm11947, ep11947, em11947, dsL]
  · norm_num [world11947, agent11947, scalar11947, tp11947, tm11947, ep11947, em11947, dsL]
  · norm_num [world11947, agent11947, scalar11947, tp11947, tm11947, ep11947, em11947, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11947, agent11947, tp11947, tm11947, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11947, agent11947, tp11947, tm11947, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11947, agent11947, scalar11947, tp11947, tm11947, ep11947, em11947, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11947, agent11947, tp11947, tm11947, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11947, agent11947, scalar11947, tp11947, tm11947, ep11947, em11947, dsL]

theorem tails11947 :
    exp (-((11947:ℝ)*ep11947)) ≤ scalar11947.upperTail ∧
    exp (-((11947:ℝ)*em11947)) ≤ scalar11947.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11947:ℝ)) (by norm_num [ep11947]) ?_)
      (show bp11947^8 ≤ scalar11947.upperTail by norm_num [bp11947, scalar11947])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11947, bp11947, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11947:ℝ)) (by norm_num [em11947]) ?_)
      (show bm11947^8 ≤ scalar11947.lowerTail by norm_num [bm11947, scalar11947])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11947, bm11947, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11947 :
    agent11947.root+dsL+scalar11947.worldRadius < √(1/100/aL) ∧
    2*(agent11947.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11947, agent11947, scalar11947, tp11947, tm11947, ep11947, em11947, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11947, agent11947, scalar11947, tp11947, tm11947, ep11947, em11947, dsL]

noncomputable def master11947 : MasterCertificate 11947 world11947 agent11947 :=
  master scalar11947 dsL tp11947 tm11947 ep11947 em11947
    (by norm_num [dsL]) (by norm_num [tp11947]) (by norm_num [tm11947])
    (by norm_num [ep11947]) (by norm_num [em11947])
    positive11947 negative11947 tails11947.1 tails11947.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11947.1 tailGuards11947.2

theorem preserves11947 : master11947.toScalarCertificate = scalar11947 := rfl

noncomputable def tp11948 : ℝ := (2419360801 / 10000000000)
noncomputable def tm11948 : ℝ := (-((6254967473 / 10000000000)))
noncomputable def ep11948 : ℝ := (56082263904264451 / 100000000000000000000)
noncomputable def em11948 : ℝ := (13501704155566369 / 25000000000000000000)
noncomputable def bp11948 : ℝ := (21637640071147794969 / 50000000000000000000)
noncomputable def bm11948 : ℝ := (44637681532778592861 / 100000000000000000000)

theorem positive11948 :
    Eplus aL (agent11948.root+dsL) scalar11948.worldRadius world11948.frame
      agent11948.frame tp11948 ≤ -ep11948 := by
  apply positive_check (eT := (116654063855006706887 / 100000000000000000000)) (y := (39758408355378974021 / 100000000000000000000)) (u := (74411246197324874161 / 50000000000000000000))
  · norm_num [world11948, agent11948, scalar11948, tp11948, tm11948, ep11948, em11948, dsL]
  · norm_num [world11948, agent11948, scalar11948, tp11948, tm11948, ep11948, em11948, dsL]
  · norm_num [world11948, agent11948, scalar11948, tp11948, tm11948, ep11948, em11948, dsL]
  · norm_num [world11948, agent11948, scalar11948, tp11948, tm11948, ep11948, em11948, dsL]
  · norm_num [world11948, agent11948, scalar11948, tp11948, tm11948, ep11948, em11948, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11948, agent11948, tp11948, tm11948, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11948, agent11948, scalar11948, tp11948, tm11948, ep11948, em11948, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11948, agent11948, tp11948, tm11948, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11948, agent11948, scalar11948, tp11948, tm11948, ep11948, em11948, dsL]

theorem negative11948 :
    Eminus aL (agent11948.root+dsL) scalar11948.worldRadius world11948.frame
      agent11948.frame tm11948 ≤ -em11948 := by
  apply negative_check (lo := (67148821426246565633 / 100000000000000000000)) (hi := (33574410713123282817 / 50000000000000000000))
    (y := (-((72867470540790688819 / 100000000000000000000)))) (u := (24127404243476749557 / 50000000000000000000))
  · norm_num [world11948, agent11948, scalar11948, tp11948, tm11948, ep11948, em11948, dsL]
  · norm_num [world11948, agent11948, scalar11948, tp11948, tm11948, ep11948, em11948, dsL]
  · norm_num [world11948, agent11948, scalar11948, tp11948, tm11948, ep11948, em11948, dsL]
  · norm_num [world11948, agent11948, scalar11948, tp11948, tm11948, ep11948, em11948, dsL]
  · norm_num [world11948, agent11948, scalar11948, tp11948, tm11948, ep11948, em11948, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11948, agent11948, tp11948, tm11948, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11948, agent11948, tp11948, tm11948, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11948, agent11948, scalar11948, tp11948, tm11948, ep11948, em11948, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11948, agent11948, tp11948, tm11948, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11948, agent11948, scalar11948, tp11948, tm11948, ep11948, em11948, dsL]

theorem tails11948 :
    exp (-((11948:ℝ)*ep11948)) ≤ scalar11948.upperTail ∧
    exp (-((11948:ℝ)*em11948)) ≤ scalar11948.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11948:ℝ)) (by norm_num [ep11948]) ?_)
      (show bp11948^8 ≤ scalar11948.upperTail by norm_num [bp11948, scalar11948])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11948, bp11948, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11948:ℝ)) (by norm_num [em11948]) ?_)
      (show bm11948^8 ≤ scalar11948.lowerTail by norm_num [bm11948, scalar11948])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11948, bm11948, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11948 :
    agent11948.root+dsL+scalar11948.worldRadius < √(1/100/aL) ∧
    2*(agent11948.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11948, agent11948, scalar11948, tp11948, tm11948, ep11948, em11948, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11948, agent11948, scalar11948, tp11948, tm11948, ep11948, em11948, dsL]

noncomputable def master11948 : MasterCertificate 11948 world11948 agent11948 :=
  master scalar11948 dsL tp11948 tm11948 ep11948 em11948
    (by norm_num [dsL]) (by norm_num [tp11948]) (by norm_num [tm11948])
    (by norm_num [ep11948]) (by norm_num [em11948])
    positive11948 negative11948 tails11948.1 tails11948.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11948.1 tailGuards11948.2

theorem preserves11948 : master11948.toScalarCertificate = scalar11948 := rfl

noncomputable def tp11949 : ℝ := (2419456707 / 10000000000)
noncomputable def tm11949 : ℝ := (-((3127590247 / 5000000000)))
noncomputable def ep11949 : ℝ := (28042543526963243 / 50000000000000000000)
noncomputable def em11949 : ℝ := (54009251585138269 / 100000000000000000000)
noncomputable def bp11949 : ℝ := (5408802736878994269 / 12500000000000000000)
noncomputable def bm11949 : ℝ := (2231652245617544929 / 5000000000000000000)

theorem positive11949 :
    Eplus aL (agent11949.root+dsL) scalar11949.worldRadius world11949.frame
      agent11949.frame tp11949 ≤ -ep11949 := by
  apply positive_check (eT := (23330866680699525977 / 20000000000000000000)) (y := (621234986485186201 / 1562500000000000000)) (u := (74411715569820621931 / 50000000000000000000))
  · norm_num [world11949, agent11949, scalar11949, tp11949, tm11949, ep11949, em11949, dsL]
  · norm_num [world11949, agent11949, scalar11949, tp11949, tm11949, ep11949, em11949, dsL]
  · norm_num [world11949, agent11949, scalar11949, tp11949, tm11949, ep11949, em11949, dsL]
  · norm_num [world11949, agent11949, scalar11949, tp11949, tm11949, ep11949, em11949, dsL]
  · norm_num [world11949, agent11949, scalar11949, tp11949, tm11949, ep11949, em11949, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11949, agent11949, tp11949, tm11949, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11949, agent11949, scalar11949, tp11949, tm11949, ep11949, em11949, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11949, agent11949, tp11949, tm11949, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11949, agent11949, scalar11949, tp11949, tm11949, ep11949, em11949, dsL]

theorem negative11949 :
    Eminus aL (agent11949.root+dsL) scalar11949.worldRadius world11949.frame
      agent11949.frame tm11949 ≤ -em11949 := by
  apply negative_check (lo := (67148569630897976719 / 100000000000000000000)) (hi := (839357120386224709 / 1250000000000000000))
    (y := (-((72867093316661066399 / 100000000000000000000)))) (u := (9650998103215628733 / 20000000000000000000))
  · norm_num [world11949, agent11949, scalar11949, tp11949, tm11949, ep11949, em11949, dsL]
  · norm_num [world11949, agent11949, scalar11949, tp11949, tm11949, ep11949, em11949, dsL]
  · norm_num [world11949, agent11949, scalar11949, tp11949, tm11949, ep11949, em11949, dsL]
  · norm_num [world11949, agent11949, scalar11949, tp11949, tm11949, ep11949, em11949, dsL]
  · norm_num [world11949, agent11949, scalar11949, tp11949, tm11949, ep11949, em11949, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11949, agent11949, tp11949, tm11949, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11949, agent11949, tp11949, tm11949, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11949, agent11949, scalar11949, tp11949, tm11949, ep11949, em11949, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11949, agent11949, tp11949, tm11949, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11949, agent11949, scalar11949, tp11949, tm11949, ep11949, em11949, dsL]

theorem tails11949 :
    exp (-((11949:ℝ)*ep11949)) ≤ scalar11949.upperTail ∧
    exp (-((11949:ℝ)*em11949)) ≤ scalar11949.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11949:ℝ)) (by norm_num [ep11949]) ?_)
      (show bp11949^8 ≤ scalar11949.upperTail by norm_num [bp11949, scalar11949])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11949, bp11949, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11949:ℝ)) (by norm_num [em11949]) ?_)
      (show bm11949^8 ≤ scalar11949.lowerTail by norm_num [bm11949, scalar11949])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11949, bm11949, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11949 :
    agent11949.root+dsL+scalar11949.worldRadius < √(1/100/aL) ∧
    2*(agent11949.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11949, agent11949, scalar11949, tp11949, tm11949, ep11949, em11949, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11949, agent11949, scalar11949, tp11949, tm11949, ep11949, em11949, dsL]

noncomputable def master11949 : MasterCertificate 11949 world11949 agent11949 :=
  master scalar11949 dsL tp11949 tm11949 ep11949 em11949
    (by norm_num [dsL]) (by norm_num [tp11949]) (by norm_num [tm11949])
    (by norm_num [ep11949]) (by norm_num [em11949])
    positive11949 negative11949 tails11949.1 tails11949.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11949.1 tailGuards11949.2

theorem preserves11949 : master11949.toScalarCertificate = scalar11949 := rfl

noncomputable def tp11950 : ℝ := (241955263 / 1000000000)
noncomputable def tm11950 : ℝ := (-((3127696773 / 5000000000)))
noncomputable def ep11950 : ℝ := (28043954342319087 / 50000000000000000000)
noncomputable def em11950 : ℝ := (54011685161890881 / 100000000000000000000)
noncomputable def bp11950 : ℝ := (8653112973895393337 / 20000000000000000000)
noncomputable def bm11950 : ℝ := (44628409425907325521 / 100000000000000000000)

theorem positive11950 :
    Eplus aL (agent11950.root+dsL) scalar11950.worldRadius world11950.frame
      agent11950.frame tp11950 ≤ -ep11950 := by
  apply positive_check (eT := (116654603120286982213 / 100000000000000000000)) (y := (39759670623221427459 / 100000000000000000000)) (u := (148824370944969727053 / 100000000000000000000))
  · norm_num [world11950, agent11950, scalar11950, tp11950, tm11950, ep11950, em11950, dsL]
  · norm_num [world11950, agent11950, scalar11950, tp11950, tm11950, ep11950, em11950, dsL]
  · norm_num [world11950, agent11950, scalar11950, tp11950, tm11950, ep11950, em11950, dsL]
  · norm_num [world11950, agent11950, scalar11950, tp11950, tm11950, ep11950, em11950, dsL]
  · norm_num [world11950, agent11950, scalar11950, tp11950, tm11950, ep11950, em11950, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11950, agent11950, tp11950, tm11950, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11950, agent11950, scalar11950, tp11950, tm11950, ep11950, em11950, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11950, agent11950, tp11950, tm11950, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11950, agent11950, scalar11950, tp11950, tm11950, ep11950, em11950, dsL]

theorem negative11950 :
    Eminus aL (agent11950.root+dsL) scalar11950.worldRadius world11950.frame
      agent11950.frame tm11950 ≤ -em11950 := by
  apply negative_check (lo := (67148317634971967719 / 100000000000000000000)) (hi := (1678707940874299193 / 2500000000000000000))
    (y := (-((72866717095705344023 / 100000000000000000000)))) (u := (24127586030903076659 / 50000000000000000000))
  · norm_num [world11950, agent11950, scalar11950, tp11950, tm11950, ep11950, em11950, dsL]
  · norm_num [world11950, agent11950, scalar11950, tp11950, tm11950, ep11950, em11950, dsL]
  · norm_num [world11950, agent11950, scalar11950, tp11950, tm11950, ep11950, em11950, dsL]
  · norm_num [world11950, agent11950, scalar11950, tp11950, tm11950, ep11950, em11950, dsL]
  · norm_num [world11950, agent11950, scalar11950, tp11950, tm11950, ep11950, em11950, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11950, agent11950, tp11950, tm11950, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11950, agent11950, tp11950, tm11950, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11950, agent11950, scalar11950, tp11950, tm11950, ep11950, em11950, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11950, agent11950, tp11950, tm11950, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11950, agent11950, scalar11950, tp11950, tm11950, ep11950, em11950, dsL]

theorem tails11950 :
    exp (-((11950:ℝ)*ep11950)) ≤ scalar11950.upperTail ∧
    exp (-((11950:ℝ)*em11950)) ≤ scalar11950.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11950:ℝ)) (by norm_num [ep11950]) ?_)
      (show bp11950^8 ≤ scalar11950.upperTail by norm_num [bp11950, scalar11950])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11950, bp11950, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11950:ℝ)) (by norm_num [em11950]) ?_)
      (show bm11950^8 ≤ scalar11950.lowerTail by norm_num [bm11950, scalar11950])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11950, bm11950, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11950 :
    agent11950.root+dsL+scalar11950.worldRadius < √(1/100/aL) ∧
    2*(agent11950.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11950, agent11950, scalar11950, tp11950, tm11950, ep11950, em11950, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11950, agent11950, scalar11950, tp11950, tm11950, ep11950, em11950, dsL]

noncomputable def master11950 : MasterCertificate 11950 world11950 agent11950 :=
  master scalar11950 dsL tp11950 tm11950 ep11950 em11950
    (by norm_num [dsL]) (by norm_num [tp11950]) (by norm_num [tm11950])
    (by norm_num [ep11950]) (by norm_num [em11950])
    positive11950 negative11950 tails11950.1 tails11950.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11950.1 tailGuards11950.2

theorem preserves11950 : master11950.toScalarCertificate = scalar11950 := rfl

noncomputable def tp11951 : ℝ := (302456059 / 1250000000)
noncomputable def tm11951 : ℝ := (-((195487693 / 312500000)))
noncomputable def ep11951 : ℝ := (14022682001773741 / 25000000000000000000)
noncomputable def em11951 : ℝ := (27007058294660789 / 50000000000000000000)
noncomputable def bp11951 : ℝ := (21630354787842379477 / 50000000000000000000)
noncomputable def bm11951 : ℝ := (22311887791097345943 / 50000000000000000000)

theorem positive11951 :
    Eplus aL (agent11951.root+dsL) scalar11951.worldRadius world11951.frame
      agent11951.frame tp11951 ≤ -ep11951 := by
  apply positive_check (eT := (116654872277533547601 / 100000000000000000000)) (y := (39760301455867804221 / 100000000000000000000)) (u := (1860316372258108133 / 1250000000000000000))
  · norm_num [world11951, agent11951, scalar11951, tp11951, tm11951, ep11951, em11951, dsL]
  · norm_num [world11951, agent11951, scalar11951, tp11951, tm11951, ep11951, em11951, dsL]
  · norm_num [world11951, agent11951, scalar11951, tp11951, tm11951, ep11951, em11951, dsL]
  · norm_num [world11951, agent11951, scalar11951, tp11951, tm11951, ep11951, em11951, dsL]
  · norm_num [world11951, agent11951, scalar11951, tp11951, tm11951, ep11951, em11951, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11951, agent11951, tp11951, tm11951, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11951, agent11951, scalar11951, tp11951, tm11951, ep11951, em11951, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11951, agent11951, tp11951, tm11951, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11951, agent11951, scalar11951, tp11951, tm11951, ep11951, em11951, dsL]

theorem negative11951 :
    Eminus aL (agent11951.root+dsL) scalar11951.worldRadius world11951.frame
      agent11951.frame tm11951 ≤ -em11951 := by
  apply negative_check (lo := (33574033687534545013 / 50000000000000000000)) (hi := (67148067375069090027 / 100000000000000000000))
    (y := (-((72866338043694695709 / 100000000000000000000)))) (u := (24127677487176381011 / 50000000000000000000))
  · norm_num [world11951, agent11951, scalar11951, tp11951, tm11951, ep11951, em11951, dsL]
  · norm_num [world11951, agent11951, scalar11951, tp11951, tm11951, ep11951, em11951, dsL]
  · norm_num [world11951, agent11951, scalar11951, tp11951, tm11951, ep11951, em11951, dsL]
  · norm_num [world11951, agent11951, scalar11951, tp11951, tm11951, ep11951, em11951, dsL]
  · norm_num [world11951, agent11951, scalar11951, tp11951, tm11951, ep11951, em11951, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11951, agent11951, tp11951, tm11951, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11951, agent11951, tp11951, tm11951, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11951, agent11951, scalar11951, tp11951, tm11951, ep11951, em11951, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11951, agent11951, tp11951, tm11951, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11951, agent11951, scalar11951, tp11951, tm11951, ep11951, em11951, dsL]

theorem tails11951 :
    exp (-((11951:ℝ)*ep11951)) ≤ scalar11951.upperTail ∧
    exp (-((11951:ℝ)*em11951)) ≤ scalar11951.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11951:ℝ)) (by norm_num [ep11951]) ?_)
      (show bp11951^8 ≤ scalar11951.upperTail by norm_num [bp11951, scalar11951])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11951, bp11951, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11951:ℝ)) (by norm_num [em11951]) ?_)
      (show bm11951^8 ≤ scalar11951.lowerTail by norm_num [bm11951, scalar11951])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11951, bm11951, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11951 :
    agent11951.root+dsL+scalar11951.worldRadius < √(1/100/aL) ∧
    2*(agent11951.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11951, agent11951, scalar11951, tp11951, tm11951, ep11951, em11951, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11951, agent11951, scalar11951, tp11951, tm11951, ep11951, em11951, dsL]

noncomputable def master11951 : MasterCertificate 11951 world11951 agent11951 :=
  master scalar11951 dsL tp11951 tm11951 ep11951 em11951
    (by norm_num [dsL]) (by norm_num [tp11951]) (by norm_num [tm11951])
    (by norm_num [ep11951]) (by norm_num [em11951])
    positive11951 negative11951 tails11951.1 tails11951.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11951.1 tailGuards11951.2

theorem preserves11951 : master11951.toScalarCertificate = scalar11951 := rfl

noncomputable def tp11952 : ℝ := (120987213 / 500000000)
noncomputable def tm11952 : ℝ := (-((625581887 / 1000000000)))
noncomputable def ep11952 : ℝ := (28046773323732223 / 50000000000000000000)
noncomputable def em11952 : ℝ := (54016547382843109 / 100000000000000000000)
noncomputable def bp11952 : ℝ := (8651170992534100711 / 20000000000000000000)
noncomputable def bm11952 : ℝ := (44619142370971602117 / 100000000000000000000)

theorem positive11952 :
    Eplus aL (agent11952.root+dsL) scalar11952.worldRadius world11952.frame
      agent11952.frame tp11952 ≤ -ep11952 := by
  apply positive_check (eT := (729094631723462541 / 625000000000000000)) (y := (39760931794267135503 / 100000000000000000000)) (u := (14882624788668073997 / 10000000000000000000))
  · norm_num [world11952, agent11952, scalar11952, tp11952, tm11952, ep11952, em11952, dsL]
  · norm_num [world11952, agent11952, scalar11952, tp11952, tm11952, ep11952, em11952, dsL]
  · norm_num [world11952, agent11952, scalar11952, tp11952, tm11952, ep11952, em11952, dsL]
  · norm_num [world11952, agent11952, scalar11952, tp11952, tm11952, ep11952, em11952, dsL]
  · norm_num [world11952, agent11952, scalar11952, tp11952, tm11952, ep11952, em11952, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11952, agent11952, tp11952, tm11952, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11952, agent11952, scalar11952, tp11952, tm11952, ep11952, em11952, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11952, agent11952, tp11952, tm11952, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11952, agent11952, scalar11952, tp11952, tm11952, ep11952, em11952, dsL]

theorem negative11952 :
    Eminus aL (agent11952.root+dsL) scalar11952.worldRadius world11952.frame
      agent11952.frame tm11952 ≤ -em11952 := by
  apply negative_check (lo := (13429563354698185577 / 20000000000000000000)) (hi := (33573908386745463943 / 50000000000000000000))
    (y := (-((9108245107190350499 / 12500000000000000000)))) (u := (48255536987222186013 / 100000000000000000000))
  · norm_num [world11952, agent11952, scalar11952, tp11952, tm11952, ep11952, em11952, dsL]
  · norm_num [world11952, agent11952, scalar11952, tp11952, tm11952, ep11952, em11952, dsL]
  · norm_num [world11952, agent11952, scalar11952, tp11952, tm11952, ep11952, em11952, dsL]
  · norm_num [world11952, agent11952, scalar11952, tp11952, tm11952, ep11952, em11952, dsL]
  · norm_num [world11952, agent11952, scalar11952, tp11952, tm11952, ep11952, em11952, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11952, agent11952, tp11952, tm11952, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11952, agent11952, tp11952, tm11952, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11952, agent11952, scalar11952, tp11952, tm11952, ep11952, em11952, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11952, agent11952, tp11952, tm11952, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11952, agent11952, scalar11952, tp11952, tm11952, ep11952, em11952, dsL]

theorem tails11952 :
    exp (-((11952:ℝ)*ep11952)) ≤ scalar11952.upperTail ∧
    exp (-((11952:ℝ)*em11952)) ≤ scalar11952.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11952:ℝ)) (by norm_num [ep11952]) ?_)
      (show bp11952^8 ≤ scalar11952.upperTail by norm_num [bp11952, scalar11952])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11952, bp11952, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11952:ℝ)) (by norm_num [em11952]) ?_)
      (show bm11952^8 ≤ scalar11952.lowerTail by norm_num [bm11952, scalar11952])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11952, bm11952, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11952 :
    agent11952.root+dsL+scalar11952.worldRadius < √(1/100/aL) ∧
    2*(agent11952.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11952, agent11952, scalar11952, tp11952, tm11952, ep11952, em11952, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11952, agent11952, scalar11952, tp11952, tm11952, ep11952, em11952, dsL]

noncomputable def master11952 : MasterCertificate 11952 world11952 agent11952 :=
  master scalar11952 dsL tp11952 tm11952 ep11952 em11952
    (by norm_num [dsL]) (by norm_num [tp11952]) (by norm_num [tm11952])
    (by norm_num [ep11952]) (by norm_num [em11952])
    positive11952 negative11952 tails11952.1 tails11952.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11952.1 tailGuards11952.2

theorem preserves11952 : master11952.toScalarCertificate = scalar11952 := rfl

noncomputable def tp11953 : ℝ := (96793597 / 400000000)
noncomputable def tm11953 : ℝ := (-((6256031419 / 10000000000)))
noncomputable def ep11953 : ℝ := (11219272657076413 / 20000000000000000000)
noncomputable def em11953 : ℝ := (54018976344617567 / 100000000000000000000)
noncomputable def bp11953 : ℝ := (8650200376737845253 / 20000000000000000000)
noncomputable def bm11953 : ℝ := (22307255295360814023 / 50000000000000000000)

theorem positive11953 :
    Eplus aL (agent11953.root+dsL) scalar11953.worldRadius world11953.frame
      agent11953.frame tp11953 ≤ -ep11953 := by
  apply positive_check (eT := (116655409002575411789 / 100000000000000000000)) (y := (19880780205184942431 / 50000000000000000000)) (u := (14882718343538057513 / 10000000000000000000))
  · norm_num [world11953, agent11953, scalar11953, tp11953, tm11953, ep11953, em11953, dsL]
  · norm_num [world11953, agent11953, scalar11953, tp11953, tm11953, ep11953, em11953, dsL]
  · norm_num [world11953, agent11953, scalar11953, tp11953, tm11953, ep11953, em11953, dsL]
  · norm_num [world11953, agent11953, scalar11953, tp11953, tm11953, ep11953, em11953, dsL]
  · norm_num [world11953, agent11953, scalar11953, tp11953, tm11953, ep11953, em11953, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11953, agent11953, tp11953, tm11953, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11953, agent11953, scalar11953, tp11953, tm11953, ep11953, em11953, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11953, agent11953, tp11953, tm11953, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11953, agent11953, scalar11953, tp11953, tm11953, ep11953, em11953, dsL]

theorem negative11953 :
    Eminus aL (agent11953.root+dsL) scalar11953.worldRadius world11953.frame
      agent11953.frame tm11953 ≤ -em11953 := by
  apply negative_check (lo := (13429513344728768989 / 20000000000000000000)) (hi := (33573783361821922473 / 50000000000000000000))
    (y := (-((72865582876439209289 / 100000000000000000000)))) (u := (6031964923046062237 / 12500000000000000000))
  · norm_num [world11953, agent11953, scalar11953, tp11953, tm11953, ep11953, em11953, dsL]
  · norm_num [world11953, agent11953, scalar11953, tp11953, tm11953, ep11953, em11953, dsL]
  · norm_num [world11953, agent11953, scalar11953, tp11953, tm11953, ep11953, em11953, dsL]
  · norm_num [world11953, agent11953, scalar11953, tp11953, tm11953, ep11953, em11953, dsL]
  · norm_num [world11953, agent11953, scalar11953, tp11953, tm11953, ep11953, em11953, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11953, agent11953, tp11953, tm11953, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11953, agent11953, tp11953, tm11953, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11953, agent11953, scalar11953, tp11953, tm11953, ep11953, em11953, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11953, agent11953, tp11953, tm11953, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11953, agent11953, scalar11953, tp11953, tm11953, ep11953, em11953, dsL]

theorem tails11953 :
    exp (-((11953:ℝ)*ep11953)) ≤ scalar11953.upperTail ∧
    exp (-((11953:ℝ)*em11953)) ≤ scalar11953.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11953:ℝ)) (by norm_num [ep11953]) ?_)
      (show bp11953^8 ≤ scalar11953.upperTail by norm_num [bp11953, scalar11953])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11953, bp11953, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11953:ℝ)) (by norm_num [em11953]) ?_)
      (show bm11953^8 ≤ scalar11953.lowerTail by norm_num [bm11953, scalar11953])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11953, bm11953, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11953 :
    agent11953.root+dsL+scalar11953.worldRadius < √(1/100/aL) ∧
    2*(agent11953.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11953, agent11953, scalar11953, tp11953, tm11953, ep11953, em11953, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11953, agent11953, scalar11953, tp11953, tm11953, ep11953, em11953, dsL]

noncomputable def master11953 : MasterCertificate 11953 world11953 agent11953 :=
  master scalar11953 dsL tp11953 tm11953 ep11953 em11953
    (by norm_num [dsL]) (by norm_num [tp11953]) (by norm_num [tm11953])
    (by norm_num [ep11953]) (by norm_num [em11953])
    positive11953 negative11953 tails11953.1 tails11953.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11953.1 tailGuards11953.2

theorem preserves11953 : master11953.toScalarCertificate = scalar11953 := rfl

noncomputable def tp11954 : ℝ := (2419935669 / 10000000000)
noncomputable def tm11954 : ℝ := (-((6256243617 / 10000000000)))
noncomputable def ep11954 : ℝ := (2243967124159801 / 4000000000000000000)
noncomputable def em11954 : ℝ := (2160856144306037 / 4000000000000000000)
noncomputable def bp11954 : ℝ := (8649230044064163901 / 20000000000000000000)
noncomputable def bm11954 : ℝ := (44609880152745887891 / 100000000000000000000)

theorem positive11954 :
    Eplus aL (agent11954.root+dsL) scalar11954.worldRadius world11954.frame
      agent11954.frame tp11954 ≤ -ep11954 := by
  apply positive_check (eT := (116655677558157430099 / 100000000000000000000)) (y := (19881095577454864273 / 50000000000000000000)) (u := (148828122157674363631 / 100000000000000000000))
  · norm_num [world11954, agent11954, scalar11954, tp11954, tm11954, ep11954, em11954, dsL]
  · norm_num [world11954, agent11954, scalar11954, tp11954, tm11954, ep11954, em11954, dsL]
  · norm_num [world11954, agent11954, scalar11954, tp11954, tm11954, ep11954, em11954, dsL]
  · norm_num [world11954, agent11954, scalar11954, tp11954, tm11954, ep11954, em11954, dsL]
  · norm_num [world11954, agent11954, scalar11954, tp11954, tm11954, ep11954, em11954, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11954, agent11954, tp11954, tm11954, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11954, agent11954, scalar11954, tp11954, tm11954, ep11954, em11954, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11954, agent11954, tp11954, tm11954, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11954, agent11954, scalar11954, tp11954, tm11954, ep11954, em11954, dsL]

theorem negative11954 :
    Eminus aL (agent11954.root+dsL) scalar11954.worldRadius world11954.frame
      agent11954.frame tm11954 ≤ -em11954 := by
  apply negative_check (lo := (67147318106134854979 / 100000000000000000000)) (hi := (3357365905306742749 / 5000000000000000000))
    (y := (-((72865202864400846507 / 100000000000000000000)))) (u := (4825590276225978587 / 10000000000000000000))
  · norm_num [world11954, agent11954, scalar11954, tp11954, tm11954, ep11954, em11954, dsL]
  · norm_num [world11954, agent11954, scalar11954, tp11954, tm11954, ep11954, em11954, dsL]
  · norm_num [world11954, agent11954, scalar11954, tp11954, tm11954, ep11954, em11954, dsL]
  · norm_num [world11954, agent11954, scalar11954, tp11954, tm11954, ep11954, em11954, dsL]
  · norm_num [world11954, agent11954, scalar11954, tp11954, tm11954, ep11954, em11954, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11954, agent11954, tp11954, tm11954, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11954, agent11954, tp11954, tm11954, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11954, agent11954, scalar11954, tp11954, tm11954, ep11954, em11954, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11954, agent11954, tp11954, tm11954, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11954, agent11954, scalar11954, tp11954, tm11954, ep11954, em11954, dsL]

theorem tails11954 :
    exp (-((11954:ℝ)*ep11954)) ≤ scalar11954.upperTail ∧
    exp (-((11954:ℝ)*em11954)) ≤ scalar11954.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11954:ℝ)) (by norm_num [ep11954]) ?_)
      (show bp11954^8 ≤ scalar11954.upperTail by norm_num [bp11954, scalar11954])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11954, bp11954, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11954:ℝ)) (by norm_num [em11954]) ?_)
      (show bm11954^8 ≤ scalar11954.lowerTail by norm_num [bm11954, scalar11954])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11954, bm11954, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11954 :
    agent11954.root+dsL+scalar11954.worldRadius < √(1/100/aL) ∧
    2*(agent11954.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11954, agent11954, scalar11954, tp11954, tm11954, ep11954, em11954, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11954, agent11954, scalar11954, tp11954, tm11954, ep11954, em11954, dsL]

noncomputable def master11954 : MasterCertificate 11954 world11954 agent11954 :=
  master scalar11954 dsL tp11954 tm11954 ep11954 em11954
    (by norm_num [dsL]) (by norm_num [tp11954]) (by norm_num [tm11954])
    (by norm_num [ep11954]) (by norm_num [em11954])
    positive11954 negative11954 tails11954.1 tails11954.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11954.1 tailGuards11954.2

theorem preserves11954 : master11954.toScalarCertificate = scalar11954 := rfl

noncomputable def tp11955 : ℝ := (2420031331 / 10000000000)
noncomputable def tm11955 : ℝ := (-((1564113993 / 2500000000)))
noncomputable def ep11955 : ℝ := (11220398282781801 / 20000000000000000000)
noncomputable def em11955 : ℝ := (6752978686688807 / 12500000000000000000)
noncomputable def bp11955 : ℝ := (4324129977179664367 / 10000000000000000000)
noncomputable def bm11955 : ℝ := (44605250842663383399 / 100000000000000000000)

theorem positive11955 :
    Eplus aL (agent11955.root+dsL) scalar11955.worldRadius world11955.frame
      agent11955.frame tp11955 ≤ -ep11955 := by
  apply positive_check (eT := (116655945546807998993 / 100000000000000000000)) (y := (39762820851470109357 / 100000000000000000000)) (u := (148829059326191125719 / 100000000000000000000))
  · norm_num [world11955, agent11955, scalar11955, tp11955, tm11955, ep11955, em11955, dsL]
  · norm_num [world11955, agent11955, scalar11955, tp11955, tm11955, ep11955, em11955, dsL]
  · norm_num [world11955, agent11955, scalar11955, tp11955, tm11955, ep11955, em11955, dsL]
  · norm_num [world11955, agent11955, scalar11955, tp11955, tm11955, ep11955, em11955, dsL]
  · norm_num [world11955, agent11955, scalar11955, tp11955, tm11955, ep11955, em11955, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11955, agent11955, tp11955, tm11955, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11955, agent11955, scalar11955, tp11955, tm11955, ep11955, em11955, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11955, agent11955, tp11955, tm11955, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11955, agent11955, scalar11955, tp11955, tm11955, ep11955, em11955, dsL]

theorem negative11955 :
    Eminus aL (agent11955.root+dsL) scalar11955.worldRadius world11955.frame
      agent11955.frame tm11955 ≤ -em11955 := by
  apply negative_check (lo := (33573534374692802639 / 50000000000000000000)) (hi := (67147068749385605279 / 100000000000000000000))
    (y := (-((9108103130984973251 / 12500000000000000000)))) (u := (24128042540688612117 / 50000000000000000000))
  · norm_num [world11955, agent11955, scalar11955, tp11955, tm11955, ep11955, em11955, dsL]
  · norm_num [world11955, agent11955, scalar11955, tp11955, tm11955, ep11955, em11955, dsL]
  · norm_num [world11955, agent11955, scalar11955, tp11955, tm11955, ep11955, em11955, dsL]
  · norm_num [world11955, agent11955, scalar11955, tp11955, tm11955, ep11955, em11955, dsL]
  · norm_num [world11955, agent11955, scalar11955, tp11955, tm11955, ep11955, em11955, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11955, agent11955, tp11955, tm11955, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11955, agent11955, tp11955, tm11955, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11955, agent11955, scalar11955, tp11955, tm11955, ep11955, em11955, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11955, agent11955, tp11955, tm11955, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11955, agent11955, scalar11955, tp11955, tm11955, ep11955, em11955, dsL]

theorem tails11955 :
    exp (-((11955:ℝ)*ep11955)) ≤ scalar11955.upperTail ∧
    exp (-((11955:ℝ)*em11955)) ≤ scalar11955.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11955:ℝ)) (by norm_num [ep11955]) ?_)
      (show bp11955^8 ≤ scalar11955.upperTail by norm_num [bp11955, scalar11955])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11955, bp11955, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11955:ℝ)) (by norm_num [em11955]) ?_)
      (show bm11955^8 ≤ scalar11955.lowerTail by norm_num [bm11955, scalar11955])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11955, bm11955, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11955 :
    agent11955.root+dsL+scalar11955.worldRadius < √(1/100/aL) ∧
    2*(agent11955.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11955, agent11955, scalar11955, tp11955, tm11955, ep11955, em11955, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11955, agent11955, scalar11955, tp11955, tm11955, ep11955, em11955, dsL]

noncomputable def master11955 : MasterCertificate 11955 world11955 agent11955 :=
  master scalar11955 dsL tp11955 tm11955 ep11955 em11955
    (by norm_num [dsL]) (by norm_num [tp11955]) (by norm_num [tm11955])
    (by norm_num [ep11955]) (by norm_num [em11955])
    positive11955 negative11955 tails11955.1 tails11955.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11955.1 tailGuards11955.2

theorem preserves11955 : master11955.toScalarCertificate = scalar11955 := rfl

noncomputable def tp11956 : ℝ := (484025381 / 2000000000)
noncomputable def tm11956 : ℝ := (-((6256668153 / 10000000000)))
noncomputable def ep11956 : ℝ := (701310038309551 / 1250000000000000000)
noncomputable def em11956 : ℝ := (10805250769133591 / 20000000000000000000)
noncomputable def bp11956 : ℝ := (675569541175507893 / 1562500000000000000)
noncomputable def bm11956 : ℝ := (44600622764787913219 / 100000000000000000000)

theorem positive11956 :
    Eplus aL (agent11956.root+dsL) scalar11956.worldRadius world11956.frame
      agent11956.frame tp11956 ≤ -ep11956 := by
  apply positive_check (eT := (116656212924048688043 / 100000000000000000000)) (y := (39763449554389810071 / 100000000000000000000)) (u := (18603749377721730279 / 12500000000000000000))
  · norm_num [world11956, agent11956, scalar11956, tp11956, tm11956, ep11956, em11956, dsL]
  · norm_num [world11956, agent11956, scalar11956, tp11956, tm11956, ep11956, em11956, dsL]
  · norm_num [world11956, agent11956, scalar11956, tp11956, tm11956, ep11956, em11956, dsL]
  · norm_num [world11956, agent11956, scalar11956, tp11956, tm11956, ep11956, em11956, dsL]
  · norm_num [world11956, agent11956, scalar11956, tp11956, tm11956, ep11956, em11956, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11956, agent11956, tp11956, tm11956, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11956, agent11956, scalar11956, tp11956, tm11956, ep11956, em11956, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11956, agent11956, tp11956, tm11956, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11956, agent11956, scalar11956, tp11956, tm11956, ep11956, em11956, dsL]

theorem negative11956 :
    Eminus aL (agent11956.root+dsL) scalar11956.worldRadius world11956.frame
      agent11956.frame tm11956 ≤ -em11956 := by
  apply negative_check (lo := (8393352508530399971 / 12500000000000000000)) (hi := (67146820068243199769 / 100000000000000000000))
    (y := (-((72864446582981110227 / 100000000000000000000)))) (u := (48256267714066332459 / 100000000000000000000))
  · norm_num [world11956, agent11956, scalar11956, tp11956, tm11956, ep11956, em11956, dsL]
  · norm_num [world11956, agent11956, scalar11956, tp11956, tm11956, ep11956, em11956, dsL]
  · norm_num [world11956, agent11956, scalar11956, tp11956, tm11956, ep11956, em11956, dsL]
  · norm_num [world11956, agent11956, scalar11956, tp11956, tm11956, ep11956, em11956, dsL]
  · norm_num [world11956, agent11956, scalar11956, tp11956, tm11956, ep11956, em11956, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11956, agent11956, tp11956, tm11956, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11956, agent11956, tp11956, tm11956, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11956, agent11956, scalar11956, tp11956, tm11956, ep11956, em11956, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11956, agent11956, tp11956, tm11956, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11956, agent11956, scalar11956, tp11956, tm11956, ep11956, em11956, dsL]

theorem tails11956 :
    exp (-((11956:ℝ)*ep11956)) ≤ scalar11956.upperTail ∧
    exp (-((11956:ℝ)*em11956)) ≤ scalar11956.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11956:ℝ)) (by norm_num [ep11956]) ?_)
      (show bp11956^8 ≤ scalar11956.upperTail by norm_num [bp11956, scalar11956])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11956, bp11956, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11956:ℝ)) (by norm_num [em11956]) ?_)
      (show bm11956^8 ≤ scalar11956.lowerTail by norm_num [bm11956, scalar11956])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11956, bm11956, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11956 :
    agent11956.root+dsL+scalar11956.worldRadius < √(1/100/aL) ∧
    2*(agent11956.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11956, agent11956, scalar11956, tp11956, tm11956, ep11956, em11956, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11956, agent11956, scalar11956, tp11956, tm11956, ep11956, em11956, dsL]

noncomputable def master11956 : MasterCertificate 11956 world11956 agent11956 :=
  master scalar11956 dsL tp11956 tm11956 ep11956 em11956
    (by norm_num [dsL]) (by norm_num [tp11956]) (by norm_num [tm11956])
    (by norm_num [ep11956]) (by norm_num [em11956])
    positive11956 negative11956 tails11956.1 tails11956.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11956.1 tailGuards11956.2

theorem preserves11956 : master11956.toScalarCertificate = scalar11956 := rfl

noncomputable def tp11957 : ℝ := (1210111237 / 5000000000)
noncomputable def tm11957 : ℝ := (-((6256880109 / 10000000000)))
noncomputable def ep11957 : ℝ := (28053806528361681 / 50000000000000000000)
noncomputable def em11957 : ℝ := (2161147066572719 / 4000000000000000000)
noncomputable def bp11957 : ℝ := (5403950351309075429 / 12500000000000000000)
noncomputable def bm11957 : ℝ := (44595995918962420819 / 100000000000000000000)

theorem positive11957 :
    Eplus aL (agent11957.root+dsL) scalar11957.worldRadius world11957.frame
      agent11957.frame tp11957 ≤ -ep11957 := by
  apply positive_check (eT := (116656480306203082677 / 100000000000000000000)) (y := (39764078734896645851 / 100000000000000000000)) (u := (37207732858509175629 / 25000000000000000000))
  · norm_num [world11957, agent11957, scalar11957, tp11957, tm11957, ep11957, em11957, dsL]
  · norm_num [world11957, agent11957, scalar11957, tp11957, tm11957, ep11957, em11957, dsL]
  · norm_num [world11957, agent11957, scalar11957, tp11957, tm11957, ep11957, em11957, dsL]
  · norm_num [world11957, agent11957, scalar11957, tp11957, tm11957, ep11957, em11957, dsL]
  · norm_num [world11957, agent11957, scalar11957, tp11957, tm11957, ep11957, em11957, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11957, agent11957, tp11957, tm11957, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11957, agent11957, scalar11957, tp11957, tm11957, ep11957, em11957, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11957, agent11957, tp11957, tm11957, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11957, agent11957, scalar11957, tp11957, tm11957, ep11957, em11957, dsL]

theorem negative11957 :
    Eminus aL (agent11957.root+dsL) scalar11957.worldRadius world11957.frame
      agent11957.frame tm11957 ≤ -em11957 := by
  apply negative_check (lo := (67146572280750453387 / 100000000000000000000)) (hi := (16786643070187613347 / 25000000000000000000))
    (y := (-((18216016746472713577 / 25000000000000000000)))) (u := (9651290178760422683 / 20000000000000000000))
  · norm_num [world11957, agent11957, scalar11957, tp11957, tm11957, ep11957, em11957, dsL]
  · norm_num [world11957, agent11957, scalar11957, tp11957, tm11957, ep11957, em11957, dsL]
  · norm_num [world11957, agent11957, scalar11957, tp11957, tm11957, ep11957, em11957, dsL]
  · norm_num [world11957, agent11957, scalar11957, tp11957, tm11957, ep11957, em11957, dsL]
  · norm_num [world11957, agent11957, scalar11957, tp11957, tm11957, ep11957, em11957, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11957, agent11957, tp11957, tm11957, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11957, agent11957, tp11957, tm11957, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11957, agent11957, scalar11957, tp11957, tm11957, ep11957, em11957, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11957, agent11957, tp11957, tm11957, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11957, agent11957, scalar11957, tp11957, tm11957, ep11957, em11957, dsL]

theorem tails11957 :
    exp (-((11957:ℝ)*ep11957)) ≤ scalar11957.upperTail ∧
    exp (-((11957:ℝ)*em11957)) ≤ scalar11957.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11957:ℝ)) (by norm_num [ep11957]) ?_)
      (show bp11957^8 ≤ scalar11957.upperTail by norm_num [bp11957, scalar11957])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11957, bp11957, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11957:ℝ)) (by norm_num [em11957]) ?_)
      (show bm11957^8 ≤ scalar11957.lowerTail by norm_num [bm11957, scalar11957])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11957, bm11957, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11957 :
    agent11957.root+dsL+scalar11957.worldRadius < √(1/100/aL) ∧
    2*(agent11957.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11957, agent11957, scalar11957, tp11957, tm11957, ep11957, em11957, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11957, agent11957, scalar11957, tp11957, tm11957, ep11957, em11957, dsL]

noncomputable def master11957 : MasterCertificate 11957 world11957 agent11957 :=
  master scalar11957 dsL tp11957 tm11957 ep11957 em11957
    (by norm_num [dsL]) (by norm_num [tp11957]) (by norm_num [tm11957])
    (by norm_num [ep11957]) (by norm_num [em11957])
    positive11957 negative11957 tails11957.1 tails11957.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11957.1 tailGuards11957.2

theorem preserves11957 : master11957.toScalarCertificate = scalar11957 := rfl

noncomputable def tp11958 : ℝ := (121015897 / 500000000)
noncomputable def tm11958 : ℝ := (-((6257092037 / 10000000000)))
noncomputable def ep11958 : ℝ := (56110421878618921 / 100000000000000000000)
noncomputable def em11958 : ℝ := (27015549199926003 / 50000000000000000000)
noncomputable def bp11958 : ℝ := (10806688995404128627 / 25000000000000000000)
noncomputable def bm11958 : ℝ := (44591370004960303673 / 100000000000000000000)

theorem positive11958 :
    Eplus aL (agent11958.root+dsL) scalar11958.worldRadius world11958.frame
      agent11958.frame tp11958 ≤ -ep11958 := by
  apply positive_check (eT := (58328373482791405053 / 50000000000000000000)) (y := (994117665081556841 / 2500000000000000000)) (u := (74415932949653524429 / 50000000000000000000))
  · norm_num [world11958, agent11958, scalar11958, tp11958, tm11958, ep11958, em11958, dsL]
  · norm_num [world11958, agent11958, scalar11958, tp11958, tm11958, ep11958, em11958, dsL]
  · norm_num [world11958, agent11958, scalar11958, tp11958, tm11958, ep11958, em11958, dsL]
  · norm_num [world11958, agent11958, scalar11958, tp11958, tm11958, ep11958, em11958, dsL]
  · norm_num [world11958, agent11958, scalar11958, tp11958, tm11958, ep11958, em11958, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11958, agent11958, tp11958, tm11958, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11958, agent11958, scalar11958, tp11958, tm11958, ep11958, em11958, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11958, agent11958, tp11958, tm11958, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11958, agent11958, scalar11958, tp11958, tm11958, ep11958, em11958, dsL]

theorem negative11958 :
    Eminus aL (agent11958.root+dsL) scalar11958.worldRadius world11958.frame
      agent11958.frame tm11958 ≤ -em11958 := by
  apply negative_check (lo := (524580660505890153 / 781250000000000000)) (hi := (13429264908950787917 / 20000000000000000000))
    (y := (-((72863688251535352127 / 100000000000000000000)))) (u := (48256633657906489291 / 100000000000000000000))
  · norm_num [world11958, agent11958, scalar11958, tp11958, tm11958, ep11958, em11958, dsL]
  · norm_num [world11958, agent11958, scalar11958, tp11958, tm11958, ep11958, em11958, dsL]
  · norm_num [world11958, agent11958, scalar11958, tp11958, tm11958, ep11958, em11958, dsL]
  · norm_num [world11958, agent11958, scalar11958, tp11958, tm11958, ep11958, em11958, dsL]
  · norm_num [world11958, agent11958, scalar11958, tp11958, tm11958, ep11958, em11958, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11958, agent11958, tp11958, tm11958, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11958, agent11958, tp11958, tm11958, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11958, agent11958, scalar11958, tp11958, tm11958, ep11958, em11958, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11958, agent11958, tp11958, tm11958, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11958, agent11958, scalar11958, tp11958, tm11958, ep11958, em11958, dsL]

theorem tails11958 :
    exp (-((11958:ℝ)*ep11958)) ≤ scalar11958.upperTail ∧
    exp (-((11958:ℝ)*em11958)) ≤ scalar11958.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11958:ℝ)) (by norm_num [ep11958]) ?_)
      (show bp11958^8 ≤ scalar11958.upperTail by norm_num [bp11958, scalar11958])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11958, bp11958, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11958:ℝ)) (by norm_num [em11958]) ?_)
      (show bm11958^8 ≤ scalar11958.lowerTail by norm_num [bm11958, scalar11958])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11958, bm11958, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11958 :
    agent11958.root+dsL+scalar11958.worldRadius < √(1/100/aL) ∧
    2*(agent11958.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11958, agent11958, scalar11958, tp11958, tm11958, ep11958, em11958, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11958, agent11958, scalar11958, tp11958, tm11958, ep11958, em11958, dsL]

noncomputable def master11958 : MasterCertificate 11958 world11958 agent11958 :=
  master scalar11958 dsL tp11958 tm11958 ep11958 em11958
    (by norm_num [dsL]) (by norm_num [tp11958]) (by norm_num [tm11958])
    (by norm_num [ep11958]) (by norm_num [em11958])
    positive11958 negative11958 tails11958.1 tails11958.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11958.1 tailGuards11958.2

theorem preserves11958 : master11958.toScalarCertificate = scalar11958 := rfl

end BstLean.Part281
