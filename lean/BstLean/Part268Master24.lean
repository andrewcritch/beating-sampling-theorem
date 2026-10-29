import BstLean.Part261Checker
import BstLean.Part268Scalar24
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12950 : ℝ := (116929897 / 500000000)
noncomputable def tm12950 : ℝ := (-((763972271 / 1250000000)))
noncomputable def ep12950 : ℝ := (52078334229458921 / 100000000000000000000)
noncomputable def em12950 : ℝ := (3167286495269283 / 6250000000000000000)
noncomputable def bp12950 : ℝ := (43040956996224508611 / 100000000000000000000)
noncomputable def bm12950 : ℝ := (22014378392040166033 / 50000000000000000000)

theorem positive12950 :
    Eplus aL (agent12950.root+dsL) scalar12950.worldRadius world12950.frame
      agent12950.frame tp12950 ≤ -ep12950 := by
  apply positive_check (eT := (11566356389772079407 / 10000000000000000000)) (y := (38030297323102158789 / 100000000000000000000)) (u := (36568192241032993743 / 25000000000000000000))
  · norm_num [world12950, agent12950, scalar12950, tp12950, tm12950, ep12950, em12950, dsL]
  · norm_num [world12950, agent12950, scalar12950, tp12950, tm12950, ep12950, em12950, dsL]
  · norm_num [world12950, agent12950, scalar12950, tp12950, tm12950, ep12950, em12950, dsL]
  · norm_num [world12950, agent12950, scalar12950, tp12950, tm12950, ep12950, em12950, dsL]
  · norm_num [world12950, agent12950, scalar12950, tp12950, tm12950, ep12950, em12950, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12950, agent12950, tp12950, tm12950, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12950, agent12950, scalar12950, tp12950, tm12950, ep12950, em12950, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12950, agent12950, tp12950, tm12950, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12950, agent12950, scalar12950, tp12950, tm12950, ep12950, em12950, dsL]

theorem negative12950 :
    Eminus aL (agent12950.root+dsL) scalar12950.worldRadius world12950.frame
      agent12950.frame tm12950 ≤ -em12950 := by
  apply negative_check (lo := (68365934051079962393 / 100000000000000000000)) (hi := (34182967025539981197 / 50000000000000000000))
    (y := (-((71645701466271450273 / 100000000000000000000)))) (u := (12211996767885250961 / 25000000000000000000))
  · norm_num [world12950, agent12950, scalar12950, tp12950, tm12950, ep12950, em12950, dsL]
  · norm_num [world12950, agent12950, scalar12950, tp12950, tm12950, ep12950, em12950, dsL]
  · norm_num [world12950, agent12950, scalar12950, tp12950, tm12950, ep12950, em12950, dsL]
  · norm_num [world12950, agent12950, scalar12950, tp12950, tm12950, ep12950, em12950, dsL]
  · norm_num [world12950, agent12950, scalar12950, tp12950, tm12950, ep12950, em12950, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12950, agent12950, tp12950, tm12950, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12950, agent12950, tp12950, tm12950, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12950, agent12950, scalar12950, tp12950, tm12950, ep12950, em12950, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12950, agent12950, tp12950, tm12950, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12950, agent12950, scalar12950, tp12950, tm12950, ep12950, em12950, dsL]

theorem tails12950 :
    exp (-((12950:ℝ)*ep12950)) ≤ scalar12950.upperTail ∧
    exp (-((12950:ℝ)*em12950)) ≤ scalar12950.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12950:ℝ)) (by norm_num [ep12950]) ?_)
      (show bp12950^8 ≤ scalar12950.upperTail by norm_num [bp12950, scalar12950])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12950, bp12950, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12950:ℝ)) (by norm_num [em12950]) ?_)
      (show bm12950^8 ≤ scalar12950.lowerTail by norm_num [bm12950, scalar12950])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12950, bm12950, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12950 :
    agent12950.root+dsL+scalar12950.worldRadius < √(1/100/aL) ∧
    2*(agent12950.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12950, agent12950, scalar12950, tp12950, tm12950, ep12950, em12950, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12950, agent12950, scalar12950, tp12950, tm12950, ep12950, em12950, dsL]

noncomputable def master12950 : MasterCertificate 12950 world12950 agent12950 :=
  master scalar12950 dsL tp12950 tm12950 ep12950 em12950
    (by norm_num [dsL]) (by norm_num [tp12950]) (by norm_num [tm12950])
    (by norm_num [ep12950]) (by norm_num [em12950])
    positive12950 negative12950 tails12950.1 tails12950.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12950.1 tailGuards12950.2

theorem preserves12950 : master12950.toScalarCertificate = scalar12950 := rfl

noncomputable def tp12951 : ℝ := (2338674999 / 10000000000)
noncomputable def tm12951 : ℝ := (-((6111942443 / 10000000000)))
noncomputable def ep12951 : ℝ := (26040333536430103 / 50000000000000000000)
noncomputable def em12951 : ℝ := (25339285056741551 / 50000000000000000000)
noncomputable def bp12951 : ℝ := (672445779222952099 / 1562500000000000000)
noncomputable def bm12951 : ℝ := (44024552253990459397 / 100000000000000000000)

theorem positive12951 :
    Eplus aL (agent12951.root+dsL) scalar12951.worldRadius world12951.frame
      agent12951.frame tp12951 ≤ -ep12951 := by
  apply positive_check (eT := (115663758611489952339 / 100000000000000000000)) (y := (594234370044832599 / 1562500000000000000)) (u := (146273796328819336353 / 100000000000000000000))
  · norm_num [world12951, agent12951, scalar12951, tp12951, tm12951, ep12951, em12951, dsL]
  · norm_num [world12951, agent12951, scalar12951, tp12951, tm12951, ep12951, em12951, dsL]
  · norm_num [world12951, agent12951, scalar12951, tp12951, tm12951, ep12951, em12951, dsL]
  · norm_num [world12951, agent12951, scalar12951, tp12951, tm12951, ep12951, em12951, dsL]
  · norm_num [world12951, agent12951, scalar12951, tp12951, tm12951, ep12951, em12951, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12951, agent12951, tp12951, tm12951, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12951, agent12951, scalar12951, tp12951, tm12951, ep12951, em12951, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12951, agent12951, tp12951, tm12951, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12951, agent12951, scalar12951, tp12951, tm12951, ep12951, em12951, dsL]

theorem negative12951 :
    Eminus aL (agent12951.root+dsL) scalar12951.worldRadius world12951.frame
      agent12951.frame tm12951 ≤ -em12951 := by
  apply negative_check (lo := (68365791146852835873 / 100000000000000000000)) (hi := (34182895573426417937 / 50000000000000000000))
    (y := (-((14329134754780952779 / 20000000000000000000)))) (u := (24424000299353287803 / 50000000000000000000))
  · norm_num [world12951, agent12951, scalar12951, tp12951, tm12951, ep12951, em12951, dsL]
  · norm_num [world12951, agent12951, scalar12951, tp12951, tm12951, ep12951, em12951, dsL]
  · norm_num [world12951, agent12951, scalar12951, tp12951, tm12951, ep12951, em12951, dsL]
  · norm_num [world12951, agent12951, scalar12951, tp12951, tm12951, ep12951, em12951, dsL]
  · norm_num [world12951, agent12951, scalar12951, tp12951, tm12951, ep12951, em12951, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12951, agent12951, tp12951, tm12951, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12951, agent12951, tp12951, tm12951, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12951, agent12951, scalar12951, tp12951, tm12951, ep12951, em12951, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12951, agent12951, tp12951, tm12951, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12951, agent12951, scalar12951, tp12951, tm12951, ep12951, em12951, dsL]

theorem tails12951 :
    exp (-((12951:ℝ)*ep12951)) ≤ scalar12951.upperTail ∧
    exp (-((12951:ℝ)*em12951)) ≤ scalar12951.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12951:ℝ)) (by norm_num [ep12951]) ?_)
      (show bp12951^8 ≤ scalar12951.upperTail by norm_num [bp12951, scalar12951])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12951, bp12951, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12951:ℝ)) (by norm_num [em12951]) ?_)
      (show bm12951^8 ≤ scalar12951.lowerTail by norm_num [bm12951, scalar12951])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12951, bm12951, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12951 :
    agent12951.root+dsL+scalar12951.worldRadius < √(1/100/aL) ∧
    2*(agent12951.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12951, agent12951, scalar12951, tp12951, tm12951, ep12951, em12951, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12951, agent12951, scalar12951, tp12951, tm12951, ep12951, em12951, dsL]

noncomputable def master12951 : MasterCertificate 12951 world12951 agent12951 :=
  master scalar12951 dsL tp12951 tm12951 ep12951 em12951
    (by norm_num [dsL]) (by norm_num [tp12951]) (by norm_num [tm12951])
    (by norm_num [ep12951]) (by norm_num [em12951])
    positive12951 negative12951 tails12951.1 tails12951.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12951.1 tailGuards12951.2

theorem preserves12951 : master12951.toScalarCertificate = scalar12951 := rfl

noncomputable def tp12952 : ℝ := (233875203 / 1000000000)
noncomputable def tm12952 : ℝ := (-((6112106281 / 10000000000)))
noncomputable def ep12952 : ℝ := (1041659966982439 / 2000000000000000000)
noncomputable def em12952 : ℝ := (50680554858002361 / 100000000000000000000)
noncomputable def bp12952 : ℝ := (2689506502532676631 / 6250000000000000000)
noncomputable def bm12952 : ℝ := (5502543617052663497 / 12500000000000000000)

theorem positive12952 :
    Eplus aL (agent12952.root+dsL) scalar12952.worldRadius world12952.frame
      agent12952.frame tp12952 ≤ -ep12952 := by
  apply positive_check (eT := (115663953156764675157 / 100000000000000000000)) (y := (38031701882510647997 / 100000000000000000000)) (u := (7313741173324941887 / 5000000000000000000))
  · norm_num [world12952, agent12952, scalar12952, tp12952, tm12952, ep12952, em12952, dsL]
  · norm_num [world12952, agent12952, scalar12952, tp12952, tm12952, ep12952, em12952, dsL]
  · norm_num [world12952, agent12952, scalar12952, tp12952, tm12952, ep12952, em12952, dsL]
  · norm_num [world12952, agent12952, scalar12952, tp12952, tm12952, ep12952, em12952, dsL]
  · norm_num [world12952, agent12952, scalar12952, tp12952, tm12952, ep12952, em12952, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12952, agent12952, tp12952, tm12952, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12952, agent12952, scalar12952, tp12952, tm12952, ep12952, em12952, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12952, agent12952, tp12952, tm12952, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12952, agent12952, scalar12952, tp12952, tm12952, ep12952, em12952, dsL]

theorem negative12952 :
    Eminus aL (agent12952.root+dsL) scalar12952.worldRadius world12952.frame
      agent12952.frame tm12952 ≤ -em12952 := by
  apply negative_check (lo := (68365650044577517511 / 100000000000000000000)) (hi := (8545706255572189689 / 12500000000000000000))
    (y := (-((35822821116332468731 / 50000000000000000000)))) (u := (48848016005974024683 / 100000000000000000000))
  · norm_num [world12952, agent12952, scalar12952, tp12952, tm12952, ep12952, em12952, dsL]
  · norm_num [world12952, agent12952, scalar12952, tp12952, tm12952, ep12952, em12952, dsL]
  · norm_num [world12952, agent12952, scalar12952, tp12952, tm12952, ep12952, em12952, dsL]
  · norm_num [world12952, agent12952, scalar12952, tp12952, tm12952, ep12952, em12952, dsL]
  · norm_num [world12952, agent12952, scalar12952, tp12952, tm12952, ep12952, em12952, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12952, agent12952, tp12952, tm12952, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12952, agent12952, tp12952, tm12952, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12952, agent12952, scalar12952, tp12952, tm12952, ep12952, em12952, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12952, agent12952, tp12952, tm12952, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12952, agent12952, scalar12952, tp12952, tm12952, ep12952, em12952, dsL]

theorem tails12952 :
    exp (-((12952:ℝ)*ep12952)) ≤ scalar12952.upperTail ∧
    exp (-((12952:ℝ)*em12952)) ≤ scalar12952.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12952:ℝ)) (by norm_num [ep12952]) ?_)
      (show bp12952^8 ≤ scalar12952.upperTail by norm_num [bp12952, scalar12952])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12952, bp12952, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12952:ℝ)) (by norm_num [em12952]) ?_)
      (show bm12952^8 ≤ scalar12952.lowerTail by norm_num [bm12952, scalar12952])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12952, bm12952, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12952 :
    agent12952.root+dsL+scalar12952.worldRadius < √(1/100/aL) ∧
    2*(agent12952.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12952, agent12952, scalar12952, tp12952, tm12952, ep12952, em12952, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12952, agent12952, scalar12952, tp12952, tm12952, ep12952, em12952, dsL]

noncomputable def master12952 : MasterCertificate 12952 world12952 agent12952 :=
  master scalar12952 dsL tp12952 tm12952 ep12952 em12952
    (by norm_num [dsL]) (by norm_num [tp12952]) (by norm_num [tm12952])
    (by norm_num [ep12952]) (by norm_num [em12952])
    positive12952 negative12952 tails12952.1 tails12952.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12952.1 tailGuards12952.2

theorem preserves12952 : master12952.toScalarCertificate = scalar12952 := rfl

noncomputable def tp12953 : ℝ := (2338829043 / 10000000000)
noncomputable def tm12953 : ℝ := (-((6112270293 / 10000000000)))
noncomputable def ep12953 : ℝ := (10417065771568641 / 20000000000000000000)
noncomputable def em12953 : ℝ := (25341269441185739 / 50000000000000000000)
noncomputable def bp12953 : ℝ := (21513839474937297863 / 50000000000000000000)
noncomputable def bm12953 : ℝ := (22008073157501465607 / 50000000000000000000)

theorem positive12953 :
    Eplus aL (agent12953.root+dsL) scalar12953.worldRadius world12953.frame
      agent12953.frame tp12953 ≤ -ep12953 := by
  apply positive_check (eT := (57832073802750544241 / 50000000000000000000)) (y := (1188512629696967881 / 3125000000000000000)) (u := (146275850711079321731 / 100000000000000000000))
  · norm_num [world12953, agent12953, scalar12953, tp12953, tm12953, ep12953, em12953, dsL]
  · norm_num [world12953, agent12953, scalar12953, tp12953, tm12953, ep12953, em12953, dsL]
  · norm_num [world12953, agent12953, scalar12953, tp12953, tm12953, ep12953, em12953, dsL]
  · norm_num [world12953, agent12953, scalar12953, tp12953, tm12953, ep12953, em12953, dsL]
  · norm_num [world12953, agent12953, scalar12953, tp12953, tm12953, ep12953, em12953, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12953, agent12953, tp12953, tm12953, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12953, agent12953, scalar12953, tp12953, tm12953, ep12953, em12953, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12953, agent12953, tp12953, tm12953, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12953, agent12953, scalar12953, tp12953, tm12953, ep12953, em12953, dsL]

theorem negative12953 :
    Eminus aL (agent12953.root+dsL) scalar12953.worldRadius world12953.frame
      agent12953.frame tm12953 ≤ -em12953 := by
  apply negative_check (lo := (34182754072585894497 / 50000000000000000000)) (hi := (13673101629034357799 / 20000000000000000000))
    (y := (-((35822806635577231463 / 50000000000000000000)))) (u := (48848030153099345467 / 100000000000000000000))
  · norm_num [world12953, agent12953, scalar12953, tp12953, tm12953, ep12953, em12953, dsL]
  · norm_num [world12953, agent12953, scalar12953, tp12953, tm12953, ep12953, em12953, dsL]
  · norm_num [world12953, agent12953, scalar12953, tp12953, tm12953, ep12953, em12953, dsL]
  · norm_num [world12953, agent12953, scalar12953, tp12953, tm12953, ep12953, em12953, dsL]
  · norm_num [world12953, agent12953, scalar12953, tp12953, tm12953, ep12953, em12953, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12953, agent12953, tp12953, tm12953, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12953, agent12953, tp12953, tm12953, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12953, agent12953, scalar12953, tp12953, tm12953, ep12953, em12953, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12953, agent12953, tp12953, tm12953, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12953, agent12953, scalar12953, tp12953, tm12953, ep12953, em12953, dsL]

theorem tails12953 :
    exp (-((12953:ℝ)*ep12953)) ≤ scalar12953.upperTail ∧
    exp (-((12953:ℝ)*em12953)) ≤ scalar12953.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12953:ℝ)) (by norm_num [ep12953]) ?_)
      (show bp12953^8 ≤ scalar12953.upperTail by norm_num [bp12953, scalar12953])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12953, bp12953, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12953:ℝ)) (by norm_num [em12953]) ?_)
      (show bm12953^8 ≤ scalar12953.lowerTail by norm_num [bm12953, scalar12953])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12953, bm12953, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12953 :
    agent12953.root+dsL+scalar12953.worldRadius < √(1/100/aL) ∧
    2*(agent12953.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12953, agent12953, scalar12953, tp12953, tm12953, ep12953, em12953, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12953, agent12953, scalar12953, tp12953, tm12953, ep12953, em12953, dsL]

noncomputable def master12953 : MasterCertificate 12953 world12953 agent12953 :=
  master scalar12953 dsL tp12953 tm12953 ep12953 em12953
    (by norm_num [dsL]) (by norm_num [tp12953]) (by norm_num [tm12953])
    (by norm_num [ep12953]) (by norm_num [em12953])
    positive12953 negative12953 tails12953.1 tails12953.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12953.1 tailGuards12953.2

theorem preserves12953 : master12953.toScalarCertificate = scalar12953 := rfl

noncomputable def tp12954 : ℝ := (18272703 / 78125000)
noncomputable def tm12954 : ℝ := (-((6112434117 / 10000000000)))
noncomputable def ep12954 : ℝ := (52087657831061251 / 100000000000000000000)
noncomputable def em12954 : ℝ := (1013690429940567 / 2000000000000000000)
noncomputable def bp12954 : ℝ := (430232551333180139 / 1000000000000000000)
noncomputable def bm12954 : ℝ := (44011944881157108901 / 100000000000000000000)

theorem positive12954 :
    Eplus aL (agent12954.root+dsL) scalar12954.worldRadius world12954.frame
      agent12954.frame tp12954 ≤ -ep12954 := by
  apply positive_check (eT := (14458042696134913487 / 12500000000000000000)) (y := (38033105590900761627 / 100000000000000000000)) (u := (146276876752879503769 / 100000000000000000000))
  · norm_num [world12954, agent12954, scalar12954, tp12954, tm12954, ep12954, em12954, dsL]
  · norm_num [world12954, agent12954, scalar12954, tp12954, tm12954, ep12954, em12954, dsL]
  · norm_num [world12954, agent12954, scalar12954, tp12954, tm12954, ep12954, em12954, dsL]
  · norm_num [world12954, agent12954, scalar12954, tp12954, tm12954, ep12954, em12954, dsL]
  · norm_num [world12954, agent12954, scalar12954, tp12954, tm12954, ep12954, em12954, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12954, agent12954, tp12954, tm12954, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12954, agent12954, scalar12954, tp12954, tm12954, ep12954, em12954, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12954, agent12954, tp12954, tm12954, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12954, agent12954, scalar12954, tp12954, tm12954, ep12954, em12954, dsL]

theorem negative12954 :
    Eminus aL (agent12954.root+dsL) scalar12954.worldRadius world12954.frame
      agent12954.frame tm12954 ≤ -em12954 := by
  apply negative_check (lo := (68365366988511853283 / 100000000000000000000)) (hi := (17091341747127963321 / 25000000000000000000))
    (y := (-((71645583270683798279 / 100000000000000000000)))) (u := (12212011201935125009 / 25000000000000000000))
  · norm_num [world12954, agent12954, scalar12954, tp12954, tm12954, ep12954, em12954, dsL]
  · norm_num [world12954, agent12954, scalar12954, tp12954, tm12954, ep12954, em12954, dsL]
  · norm_num [world12954, agent12954, scalar12954, tp12954, tm12954, ep12954, em12954, dsL]
  · norm_num [world12954, agent12954, scalar12954, tp12954, tm12954, ep12954, em12954, dsL]
  · norm_num [world12954, agent12954, scalar12954, tp12954, tm12954, ep12954, em12954, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12954, agent12954, tp12954, tm12954, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12954, agent12954, tp12954, tm12954, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12954, agent12954, scalar12954, tp12954, tm12954, ep12954, em12954, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12954, agent12954, tp12954, tm12954, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12954, agent12954, scalar12954, tp12954, tm12954, ep12954, em12954, dsL]

theorem tails12954 :
    exp (-((12954:ℝ)*ep12954)) ≤ scalar12954.upperTail ∧
    exp (-((12954:ℝ)*em12954)) ≤ scalar12954.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12954:ℝ)) (by norm_num [ep12954]) ?_)
      (show bp12954^8 ≤ scalar12954.upperTail by norm_num [bp12954, scalar12954])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12954, bp12954, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12954:ℝ)) (by norm_num [em12954]) ?_)
      (show bm12954^8 ≤ scalar12954.lowerTail by norm_num [bm12954, scalar12954])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12954, bm12954, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12954 :
    agent12954.root+dsL+scalar12954.worldRadius < √(1/100/aL) ∧
    2*(agent12954.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12954, agent12954, scalar12954, tp12954, tm12954, ep12954, em12954, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12954, agent12954, scalar12954, tp12954, tm12954, ep12954, em12954, dsL]

noncomputable def master12954 : MasterCertificate 12954 world12954 agent12954 :=
  master scalar12954 dsL tp12954 tm12954 ep12954 em12954
    (by norm_num [dsL]) (by norm_num [tp12954]) (by norm_num [tm12954])
    (by norm_num [ep12954]) (by norm_num [em12954])
    positive12954 negative12954 tails12954.1 tails12954.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12954.1 tailGuards12954.2

theorem preserves12954 : master12954.toScalarCertificate = scalar12954 := rfl

noncomputable def tp12955 : ℝ := (2338982897 / 10000000000)
noncomputable def tm12955 : ℝ := (-((122251953 / 200000000)))
noncomputable def ep12955 : ℝ := (26044993002621111 / 50000000000000000000)
noncomputable def em12955 : ℝ := (5068650335684911 / 10000000000000000000)
noncomputable def bp12955 : ℝ := (5377354009719048447 / 12500000000000000000)
noncomputable def bm12955 : ℝ := (8801548833631051707 / 20000000000000000000)

theorem positive12955 :
    Eplus aL (agent12955.root+dsL) scalar12955.worldRadius world12955.frame
      agent12955.frame tp12955 ≤ -ep12955 := by
  apply positive_check (eT := (115664535364171543707 / 100000000000000000000)) (y := (19016903411343864697 / 50000000000000000000)) (u := (29255580499286538869 / 20000000000000000000))
  · norm_num [world12955, agent12955, scalar12955, tp12955, tm12955, ep12955, em12955, dsL]
  · norm_num [world12955, agent12955, scalar12955, tp12955, tm12955, ep12955, em12955, dsL]
  · norm_num [world12955, agent12955, scalar12955, tp12955, tm12955, ep12955, em12955, dsL]
  · norm_num [world12955, agent12955, scalar12955, tp12955, tm12955, ep12955, em12955, dsL]
  · norm_num [world12955, agent12955, scalar12955, tp12955, tm12955, ep12955, em12955, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12955, agent12955, tp12955, tm12955, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12955, agent12955, scalar12955, tp12955, tm12955, ep12955, em12955, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12955, agent12955, tp12955, tm12955, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12955, agent12955, scalar12955, tp12955, tm12955, ep12955, em12955, dsL]

theorem negative12955 :
    Eminus aL (agent12955.root+dsL) scalar12955.worldRadius world12955.frame
      agent12955.frame tm12955 ≤ -em12955 := by
  apply negative_check (lo := (8545653376580167583 / 12500000000000000000)) (hi := (13673045402528268133 / 20000000000000000000))
    (y := (-((8955693869805184563 / 12500000000000000000)))) (u := (12212015147910414457 / 25000000000000000000))
  · norm_num [world12955, agent12955, scalar12955, tp12955, tm12955, ep12955, em12955, dsL]
  · norm_num [world12955, agent12955, scalar12955, tp12955, tm12955, ep12955, em12955, dsL]
  · norm_num [world12955, agent12955, scalar12955, tp12955, tm12955, ep12955, em12955, dsL]
  · norm_num [world12955, agent12955, scalar12955, tp12955, tm12955, ep12955, em12955, dsL]
  · norm_num [world12955, agent12955, scalar12955, tp12955, tm12955, ep12955, em12955, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12955, agent12955, tp12955, tm12955, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12955, agent12955, tp12955, tm12955, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12955, agent12955, scalar12955, tp12955, tm12955, ep12955, em12955, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12955, agent12955, tp12955, tm12955, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12955, agent12955, scalar12955, tp12955, tm12955, ep12955, em12955, dsL]

theorem tails12955 :
    exp (-((12955:ℝ)*ep12955)) ≤ scalar12955.upperTail ∧
    exp (-((12955:ℝ)*em12955)) ≤ scalar12955.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12955:ℝ)) (by norm_num [ep12955]) ?_)
      (show bp12955^8 ≤ scalar12955.upperTail by norm_num [bp12955, scalar12955])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12955, bp12955, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12955:ℝ)) (by norm_num [em12955]) ?_)
      (show bm12955^8 ≤ scalar12955.lowerTail by norm_num [bm12955, scalar12955])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12955, bm12955, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12955 :
    agent12955.root+dsL+scalar12955.worldRadius < √(1/100/aL) ∧
    2*(agent12955.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12955, agent12955, scalar12955, tp12955, tm12955, ep12955, em12955, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12955, agent12955, scalar12955, tp12955, tm12955, ep12955, em12955, dsL]

noncomputable def master12955 : MasterCertificate 12955 world12955 agent12955 :=
  master scalar12955 dsL tp12955 tm12955 ep12955 em12955
    (by norm_num [dsL]) (by norm_num [tp12955]) (by norm_num [tm12955])
    (by norm_num [ep12955]) (by norm_num [em12955])
    positive12955 negative12955 tails12955.1 tails12955.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12955.1 tailGuards12955.2

theorem preserves12955 : master12955.toScalarCertificate = scalar12955 := rfl

noncomputable def tp12956 : ℝ := (2339059809 / 10000000000)
noncomputable def tm12956 : ℝ := (-((6112761441 / 10000000000)))
noncomputable def ep12956 : ℝ := (13023078117206459 / 25000000000000000000)
noncomputable def em12956 : ℝ := (50688483622382773 / 100000000000000000000)
noncomputable def bp12956 : ℝ := (21507205209087527523 / 50000000000000000000)
noncomputable def bm12956 : ℝ := (8800708954843251193 / 20000000000000000000)

theorem positive12956 :
    Eplus aL (agent12956.root+dsL) scalar12956.worldRadius world12956.frame
      agent12956.frame tp12956 ≤ -ep12956 := by
  apply positive_check (eT := (115664729185063827221 / 100000000000000000000)) (y := (38034508517830954733 / 100000000000000000000)) (u := (1462789289249713191 / 1000000000000000000))
  · norm_num [world12956, agent12956, scalar12956, tp12956, tm12956, ep12956, em12956, dsL]
  · norm_num [world12956, agent12956, scalar12956, tp12956, tm12956, ep12956, em12956, dsL]
  · norm_num [world12956, agent12956, scalar12956, tp12956, tm12956, ep12956, em12956, dsL]
  · norm_num [world12956, agent12956, scalar12956, tp12956, tm12956, ep12956, em12956, dsL]
  · norm_num [world12956, agent12956, scalar12956, tp12956, tm12956, ep12956, em12956, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12956, agent12956, tp12956, tm12956, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12956, agent12956, scalar12956, tp12956, tm12956, ep12956, em12956, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12956, agent12956, tp12956, tm12956, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12956, agent12956, scalar12956, tp12956, tm12956, ep12956, em12956, dsL]

theorem negative12956 :
    Eminus aL (agent12956.root+dsL) scalar12956.worldRadius world12956.frame
      agent12956.frame tm12956 ≤ -em12956 := by
  apply negative_check (lo := (13673017176482584561 / 20000000000000000000)) (hi := (34182542941206461403 / 50000000000000000000))
    (y := (-((71645521778569671617 / 100000000000000000000)))) (u := (48848074845445197263 / 100000000000000000000))
  · norm_num [world12956, agent12956, scalar12956, tp12956, tm12956, ep12956, em12956, dsL]
  · norm_num [world12956, agent12956, scalar12956, tp12956, tm12956, ep12956, em12956, dsL]
  · norm_num [world12956, agent12956, scalar12956, tp12956, tm12956, ep12956, em12956, dsL]
  · norm_num [world12956, agent12956, scalar12956, tp12956, tm12956, ep12956, em12956, dsL]
  · norm_num [world12956, agent12956, scalar12956, tp12956, tm12956, ep12956, em12956, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12956, agent12956, tp12956, tm12956, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12956, agent12956, tp12956, tm12956, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12956, agent12956, scalar12956, tp12956, tm12956, ep12956, em12956, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12956, agent12956, tp12956, tm12956, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12956, agent12956, scalar12956, tp12956, tm12956, ep12956, em12956, dsL]

theorem tails12956 :
    exp (-((12956:ℝ)*ep12956)) ≤ scalar12956.upperTail ∧
    exp (-((12956:ℝ)*em12956)) ≤ scalar12956.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12956:ℝ)) (by norm_num [ep12956]) ?_)
      (show bp12956^8 ≤ scalar12956.upperTail by norm_num [bp12956, scalar12956])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12956, bp12956, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12956:ℝ)) (by norm_num [em12956]) ?_)
      (show bm12956^8 ≤ scalar12956.lowerTail by norm_num [bm12956, scalar12956])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12956, bm12956, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12956 :
    agent12956.root+dsL+scalar12956.worldRadius < √(1/100/aL) ∧
    2*(agent12956.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12956, agent12956, scalar12956, tp12956, tm12956, ep12956, em12956, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12956, agent12956, scalar12956, tp12956, tm12956, ep12956, em12956, dsL]

noncomputable def master12956 : MasterCertificate 12956 world12956 agent12956 :=
  master scalar12956 dsL tp12956 tm12956 ep12956 em12956
    (by norm_num [dsL]) (by norm_num [tp12956]) (by norm_num [tm12956])
    (by norm_num [ep12956]) (by norm_num [em12956])
    positive12956 negative12956 tails12956.1 tails12956.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12956.1 tailGuards12956.2

theorem preserves12956 : master12956.toScalarCertificate = scalar12956 := rfl

noncomputable def tp12957 : ℝ := (233913669 / 1000000000)
noncomputable def tm12957 : ℝ := (-((382057797 / 625000000)))
noncomputable def ep12957 : ℝ := (52094637841596529 / 100000000000000000000)
noncomputable def em12957 : ℝ := (50690462884621553 / 100000000000000000000)
noncomputable def bp12957 : ℝ := (8601997944556548839 / 20000000000000000000)
noncomputable def bm12957 : ℝ := (21999673139073286203 / 50000000000000000000)

theorem positive12957 :
    Eplus aL (agent12957.root+dsL) scalar12957.worldRadius world12957.frame
      agent12957.frame tp12957 ≤ -ep12957 := by
  apply positive_check (eT := (4626596912636390799 / 4000000000000000000)) (y := (38035209950597735617 / 100000000000000000000)) (u := (146279954976908223007 / 100000000000000000000))
  · norm_num [world12957, agent12957, scalar12957, tp12957, tm12957, ep12957, em12957, dsL]
  · norm_num [world12957, agent12957, scalar12957, tp12957, tm12957, ep12957, em12957, dsL]
  · norm_num [world12957, agent12957, scalar12957, tp12957, tm12957, ep12957, em12957, dsL]
  · norm_num [world12957, agent12957, scalar12957, tp12957, tm12957, ep12957, em12957, dsL]
  · norm_num [world12957, agent12957, scalar12957, tp12957, tm12957, ep12957, em12957, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12957, agent12957, tp12957, tm12957, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12957, agent12957, scalar12957, tp12957, tm12957, ep12957, em12957, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12957, agent12957, tp12957, tm12957, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12957, agent12957, scalar12957, tp12957, tm12957, ep12957, em12957, dsL]

theorem negative12957 :
    Eminus aL (agent12957.root+dsL) scalar12957.worldRadius world12957.frame
      agent12957.frame tm12957 ≤ -em12957 := by
  apply negative_check (lo := (68364946736762604779 / 100000000000000000000)) (hi := (3418247336838130239 / 5000000000000000000))
    (y := (-((17911372115723523017 / 25000000000000000000)))) (u := (9769618223902810107 / 20000000000000000000))
  · norm_num [world12957, agent12957, scalar12957, tp12957, tm12957, ep12957, em12957, dsL]
  · norm_num [world12957, agent12957, scalar12957, tp12957, tm12957, ep12957, em12957, dsL]
  · norm_num [world12957, agent12957, scalar12957, tp12957, tm12957, ep12957, em12957, dsL]
  · norm_num [world12957, agent12957, scalar12957, tp12957, tm12957, ep12957, em12957, dsL]
  · norm_num [world12957, agent12957, scalar12957, tp12957, tm12957, ep12957, em12957, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12957, agent12957, tp12957, tm12957, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12957, agent12957, tp12957, tm12957, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12957, agent12957, scalar12957, tp12957, tm12957, ep12957, em12957, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12957, agent12957, tp12957, tm12957, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12957, agent12957, scalar12957, tp12957, tm12957, ep12957, em12957, dsL]

theorem tails12957 :
    exp (-((12957:ℝ)*ep12957)) ≤ scalar12957.upperTail ∧
    exp (-((12957:ℝ)*em12957)) ≤ scalar12957.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12957:ℝ)) (by norm_num [ep12957]) ?_)
      (show bp12957^8 ≤ scalar12957.upperTail by norm_num [bp12957, scalar12957])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12957, bp12957, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12957:ℝ)) (by norm_num [em12957]) ?_)
      (show bm12957^8 ≤ scalar12957.lowerTail by norm_num [bm12957, scalar12957])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12957, bm12957, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12957 :
    agent12957.root+dsL+scalar12957.worldRadius < √(1/100/aL) ∧
    2*(agent12957.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12957, agent12957, scalar12957, tp12957, tm12957, ep12957, em12957, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12957, agent12957, scalar12957, tp12957, tm12957, ep12957, em12957, dsL]

noncomputable def master12957 : MasterCertificate 12957 world12957 agent12957 :=
  master scalar12957 dsL tp12957 tm12957 ep12957 em12957
    (by norm_num [dsL]) (by norm_num [tp12957]) (by norm_num [tm12957])
    (by norm_num [ep12957]) (by norm_num [em12957])
    positive12957 negative12957 tails12957.1 tails12957.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12957.1 tailGuards12957.2

theorem preserves12957 : master12957.toScalarCertificate = scalar12957 := rfl

noncomputable def tp12958 : ℝ := (1169606739 / 5000000000)
noncomputable def tm12958 : ℝ := (-((611308847 / 1000000000)))
noncomputable def ep12958 : ℝ := (52096962770434983 / 100000000000000000000)
noncomputable def em12958 : ℝ := (25346220882800089 / 50000000000000000000)
noncomputable def bp12958 : ℝ := (43005569540941603943 / 100000000000000000000)
noncomputable def bm12958 : ℝ := (4399514823666214343 / 10000000000000000000)

theorem positive12958 :
    Eplus aL (agent12958.root+dsL) scalar12958.worldRadius world12958.frame
      agent12958.frame tp12958 ≤ -ep12958 := by
  apply positive_check (eT := (23133023162100946661 / 20000000000000000000)) (y := (38035909938103038517 / 100000000000000000000)) (u := (1142820147827340339 / 781250000000000000))
  · norm_num [world12958, agent12958, scalar12958, tp12958, tm12958, ep12958, em12958, dsL]
  · norm_num [world12958, agent12958, scalar12958, tp12958, tm12958, ep12958, em12958, dsL]
  · norm_num [world12958, agent12958, scalar12958, tp12958, tm12958, ep12958, em12958, dsL]
  · norm_num [world12958, agent12958, scalar12958, tp12958, tm12958, ep12958, em12958, dsL]
  · norm_num [world12958, agent12958, scalar12958, tp12958, tm12958, ep12958, em12958, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12958, agent12958, tp12958, tm12958, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12958, agent12958, scalar12958, tp12958, tm12958, ep12958, em12958, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12958, agent12958, tp12958, tm12958, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12958, agent12958, scalar12958, tp12958, tm12958, ep12958, em12958, dsL]

theorem negative12958 :
    Eminus aL (agent12958.root+dsL) scalar12958.worldRadius world12958.frame
      agent12958.frame tm12958 ≤ -em12958 := by
  apply negative_check (lo := (68364805803110670371 / 100000000000000000000)) (hi := (17091201450777667593 / 25000000000000000000))
    (y := (-((71645459807899107763 / 100000000000000000000)))) (u := (610601313961676453 / 1250000000000000000))
  · norm_num [world12958, agent12958, scalar12958, tp12958, tm12958, ep12958, em12958, dsL]
  · norm_num [world12958, agent12958, scalar12958, tp12958, tm12958, ep12958, em12958, dsL]
  · norm_num [world12958, agent12958, scalar12958, tp12958, tm12958, ep12958, em12958, dsL]
  · norm_num [world12958, agent12958, scalar12958, tp12958, tm12958, ep12958, em12958, dsL]
  · norm_num [world12958, agent12958, scalar12958, tp12958, tm12958, ep12958, em12958, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12958, agent12958, tp12958, tm12958, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12958, agent12958, tp12958, tm12958, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12958, agent12958, scalar12958, tp12958, tm12958, ep12958, em12958, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12958, agent12958, tp12958, tm12958, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12958, agent12958, scalar12958, tp12958, tm12958, ep12958, em12958, dsL]

theorem tails12958 :
    exp (-((12958:ℝ)*ep12958)) ≤ scalar12958.upperTail ∧
    exp (-((12958:ℝ)*em12958)) ≤ scalar12958.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12958:ℝ)) (by norm_num [ep12958]) ?_)
      (show bp12958^8 ≤ scalar12958.upperTail by norm_num [bp12958, scalar12958])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12958, bp12958, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12958:ℝ)) (by norm_num [em12958]) ?_)
      (show bm12958^8 ≤ scalar12958.lowerTail by norm_num [bm12958, scalar12958])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12958, bm12958, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12958 :
    agent12958.root+dsL+scalar12958.worldRadius < √(1/100/aL) ∧
    2*(agent12958.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12958, agent12958, scalar12958, tp12958, tm12958, ep12958, em12958, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12958, agent12958, scalar12958, tp12958, tm12958, ep12958, em12958, dsL]

noncomputable def master12958 : MasterCertificate 12958 world12958 agent12958 :=
  master scalar12958 dsL tp12958 tm12958 ep12958 em12958
    (by norm_num [dsL]) (by norm_num [tp12958]) (by norm_num [tm12958])
    (by norm_num [ep12958]) (by norm_num [em12958])
    positive12958 negative12958 tails12958.1 tails12958.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12958.1 tailGuards12958.2

theorem preserves12958 : master12958.toScalarCertificate = scalar12958 := rfl

noncomputable def tp12959 : ℝ := (467858053 / 2000000000)
noncomputable def tm12959 : ℝ := (-((6113251781 / 10000000000)))
noncomputable def ep12959 : ℝ := (6512410726695387 / 12500000000000000000)
noncomputable def em12959 : ℝ := (50694418867726229 / 100000000000000000000)
noncomputable def bp12959 : ℝ := (21500575438475132699 / 50000000000000000000)
noncomputable def bm12959 : ℝ := (8798190329138867353 / 20000000000000000000)

theorem positive12959 :
    Eplus aL (agent12959.root+dsL) scalar12959.worldRadius world12959.frame
      agent12959.frame tp12959 ≤ -ep12959 := by
  apply positive_check (eT := (115665308830952744401 / 100000000000000000000)) (y := (38036610438793155089 / 100000000000000000000)) (u := (73141001812377720837 / 50000000000000000000))
  · norm_num [world12959, agent12959, scalar12959, tp12959, tm12959, ep12959, em12959, dsL]
  · norm_num [world12959, agent12959, scalar12959, tp12959, tm12959, ep12959, em12959, dsL]
  · norm_num [world12959, agent12959, scalar12959, tp12959, tm12959, ep12959, em12959, dsL]
  · norm_num [world12959, agent12959, scalar12959, tp12959, tm12959, ep12959, em12959, dsL]
  · norm_num [world12959, agent12959, scalar12959, tp12959, tm12959, ep12959, em12959, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12959, agent12959, tp12959, tm12959, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12959, agent12959, scalar12959, tp12959, tm12959, ep12959, em12959, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12959, agent12959, tp12959, tm12959, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12959, agent12959, scalar12959, tp12959, tm12959, ep12959, em12959, dsL]

theorem negative12959 :
    Eminus aL (agent12959.root+dsL) scalar12959.worldRadius world12959.frame
      agent12959.frame tm12959 ≤ -em12959 := by
  apply negative_check (lo := (8545583317935205849 / 12500000000000000000)) (hi := (68364666543481646793 / 100000000000000000000))
    (y := (-((7164542775400738989 / 10000000000000000000)))) (u := (4884812077465534611 / 10000000000000000000))
  · norm_num [world12959, agent12959, scalar12959, tp12959, tm12959, ep12959, em12959, dsL]
  · norm_num [world12959, agent12959, scalar12959, tp12959, tm12959, ep12959, em12959, dsL]
  · norm_num [world12959, agent12959, scalar12959, tp12959, tm12959, ep12959, em12959, dsL]
  · norm_num [world12959, agent12959, scalar12959, tp12959, tm12959, ep12959, em12959, dsL]
  · norm_num [world12959, agent12959, scalar12959, tp12959, tm12959, ep12959, em12959, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12959, agent12959, tp12959, tm12959, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12959, agent12959, tp12959, tm12959, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12959, agent12959, scalar12959, tp12959, tm12959, ep12959, em12959, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12959, agent12959, tp12959, tm12959, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12959, agent12959, scalar12959, tp12959, tm12959, ep12959, em12959, dsL]

theorem tails12959 :
    exp (-((12959:ℝ)*ep12959)) ≤ scalar12959.upperTail ∧
    exp (-((12959:ℝ)*em12959)) ≤ scalar12959.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12959:ℝ)) (by norm_num [ep12959]) ?_)
      (show bp12959^8 ≤ scalar12959.upperTail by norm_num [bp12959, scalar12959])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12959, bp12959, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12959:ℝ)) (by norm_num [em12959]) ?_)
      (show bm12959^8 ≤ scalar12959.lowerTail by norm_num [bm12959, scalar12959])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12959, bm12959, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12959 :
    agent12959.root+dsL+scalar12959.worldRadius < √(1/100/aL) ∧
    2*(agent12959.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12959, agent12959, scalar12959, tp12959, tm12959, ep12959, em12959, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12959, agent12959, scalar12959, tp12959, tm12959, ep12959, em12959, dsL]

noncomputable def master12959 : MasterCertificate 12959 world12959 agent12959 :=
  master scalar12959 dsL tp12959 tm12959 ep12959 em12959
    (by norm_num [dsL]) (by norm_num [tp12959]) (by norm_num [tm12959])
    (by norm_num [ep12959]) (by norm_num [em12959])
    positive12959 negative12959 tails12959.1 tails12959.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12959.1 tailGuards12959.2

theorem preserves12959 : master12959.toScalarCertificate = scalar12959 := rfl

noncomputable def tp12960 : ℝ := (584859797 / 2500000000)
noncomputable def tm12960 : ℝ := (-((1222726693 / 2000000000)))
noncomputable def ep12960 : ℝ := (52102975246178533 / 100000000000000000000)
noncomputable def em12960 : ℝ := (1267447177994849 / 2500000000000000000)
noncomputable def bp12960 : ℝ := (42995780673198677637 / 100000000000000000000)
noncomputable def bm12960 : ℝ := (43985692678717796039 / 100000000000000000000)

theorem positive12960 :
    Eplus aL (agent12960.root+dsL) scalar12960.worldRadius world12960.frame
      agent12960.frame tp12960 ≤ -ep12960 := by
  apply positive_check (eT := (115666020944575509233 / 100000000000000000000)) (y := (9509148450311589999 / 25000000000000000000)) (u := (146281979287020660407 / 100000000000000000000))
  · norm_num [world12960, agent12960, scalar12960, tp12960, tm12960, ep12960, em12960, dsL]
  · norm_num [world12960, agent12960, scalar12960, tp12960, tm12960, ep12960, em12960, dsL]
  · norm_num [world12960, agent12960, scalar12960, tp12960, tm12960, ep12960, em12960, dsL]
  · norm_num [world12960, agent12960, scalar12960, tp12960, tm12960, ep12960, em12960, dsL]
  · norm_num [world12960, agent12960, scalar12960, tp12960, tm12960, ep12960, em12960, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12960, agent12960, tp12960, tm12960, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12960, agent12960, scalar12960, tp12960, tm12960, ep12960, em12960, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12960, agent12960, tp12960, tm12960, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12960, agent12960, scalar12960, tp12960, tm12960, ep12960, em12960, dsL]

theorem negative12960 :
    Eminus aL (agent12960.root+dsL) scalar12960.worldRadius world12960.frame
      agent12960.frame tm12960 ≤ -em12960 := by
  apply negative_check (lo := (136727197001614197 / 200000000000000000)) (hi := (68363598500807098501 / 100000000000000000000))
    (y := (-((35821759404209106297 / 50000000000000000000)))) (u := (48849053267602633067 / 100000000000000000000))
  · norm_num [world12960, agent12960, scalar12960, tp12960, tm12960, ep12960, em12960, dsL]
  · norm_num [world12960, agent12960, scalar12960, tp12960, tm12960, ep12960, em12960, dsL]
  · norm_num [world12960, agent12960, scalar12960, tp12960, tm12960, ep12960, em12960, dsL]
  · norm_num [world12960, agent12960, scalar12960, tp12960, tm12960, ep12960, em12960, dsL]
  · norm_num [world12960, agent12960, scalar12960, tp12960, tm12960, ep12960, em12960, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12960, agent12960, tp12960, tm12960, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12960, agent12960, tp12960, tm12960, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12960, agent12960, scalar12960, tp12960, tm12960, ep12960, em12960, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12960, agent12960, tp12960, tm12960, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12960, agent12960, scalar12960, tp12960, tm12960, ep12960, em12960, dsL]

theorem tails12960 :
    exp (-((12960:ℝ)*ep12960)) ≤ scalar12960.upperTail ∧
    exp (-((12960:ℝ)*em12960)) ≤ scalar12960.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12960:ℝ)) (by norm_num [ep12960]) ?_)
      (show bp12960^8 ≤ scalar12960.upperTail by norm_num [bp12960, scalar12960])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12960, bp12960, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12960:ℝ)) (by norm_num [em12960]) ?_)
      (show bm12960^8 ≤ scalar12960.lowerTail by norm_num [bm12960, scalar12960])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12960, bm12960, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12960 :
    agent12960.root+dsL+scalar12960.worldRadius < √(1/100/aL) ∧
    2*(agent12960.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12960, agent12960, scalar12960, tp12960, tm12960, ep12960, em12960, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12960, agent12960, scalar12960, tp12960, tm12960, ep12960, em12960, dsL]

noncomputable def master12960 : MasterCertificate 12960 world12960 agent12960 :=
  master scalar12960 dsL tp12960 tm12960 ep12960 em12960
    (by norm_num [dsL]) (by norm_num [tp12960]) (by norm_num [tm12960])
    (by norm_num [ep12960]) (by norm_num [em12960])
    positive12960 negative12960 tails12960.1 tails12960.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12960.1 tailGuards12960.2

theorem preserves12960 : master12960.toScalarCertificate = scalar12960 := rfl

noncomputable def tp12961 : ℝ := (584878973 / 2500000000)
noncomputable def tm12961 : ℝ := (-((764224597 / 1250000000)))
noncomputable def ep12961 : ℝ := (52105296044653071 / 100000000000000000000)
noncomputable def em12961 : ℝ := (50699862143489269 / 100000000000000000000)
noncomputable def bp12961 : ℝ := (671740062587923201 / 1562500000000000000)
noncomputable def bm12961 : ℝ := (21990748976965609863 / 50000000000000000000)

theorem positive12961 :
    Eplus aL (agent12961.root+dsL) scalar12961.worldRadius world12961.frame
      agent12961.frame tp12961 ≤ -ep12961 := by
  apply positive_check (eT := (28916553355897801463 / 25000000000000000000)) (y := (19018646745109120341 / 50000000000000000000)) (u := (4571343837796197287 / 3125000000000000000))
  · norm_num [world12961, agent12961, scalar12961, tp12961, tm12961, ep12961, em12961, dsL]
  · norm_num [world12961, agent12961, scalar12961, tp12961, tm12961, ep12961, em12961, dsL]
  · norm_num [world12961, agent12961, scalar12961, tp12961, tm12961, ep12961, em12961, dsL]
  · norm_num [world12961, agent12961, scalar12961, tp12961, tm12961, ep12961, em12961, dsL]
  · norm_num [world12961, agent12961, scalar12961, tp12961, tm12961, ep12961, em12961, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12961, agent12961, tp12961, tm12961, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12961, agent12961, scalar12961, tp12961, tm12961, ep12961, em12961, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12961, agent12961, tp12961, tm12961, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12961, agent12961, scalar12961, tp12961, tm12961, ep12961, em12961, dsL]

theorem negative12961 :
    Eminus aL (agent12961.root+dsL) scalar12961.worldRadius world12961.frame
      agent12961.frame tm12961 ≤ -em12961 := by
  apply negative_check (lo := (68363459148939773459 / 100000000000000000000)) (hi := (3418172957446988673 / 5000000000000000000))
    (y := (-((7164348792424330791 / 10000000000000000000)))) (u := (24424534177116006603 / 50000000000000000000))
  · norm_num [world12961, agent12961, scalar12961, tp12961, tm12961, ep12961, em12961, dsL]
  · norm_num [world12961, agent12961, scalar12961, tp12961, tm12961, ep12961, em12961, dsL]
  · norm_num [world12961, agent12961, scalar12961, tp12961, tm12961, ep12961, em12961, dsL]
  · norm_num [world12961, agent12961, scalar12961, tp12961, tm12961, ep12961, em12961, dsL]
  · norm_num [world12961, agent12961, scalar12961, tp12961, tm12961, ep12961, em12961, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12961, agent12961, tp12961, tm12961, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12961, agent12961, tp12961, tm12961, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12961, agent12961, scalar12961, tp12961, tm12961, ep12961, em12961, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12961, agent12961, tp12961, tm12961, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12961, agent12961, scalar12961, tp12961, tm12961, ep12961, em12961, dsL]

theorem tails12961 :
    exp (-((12961:ℝ)*ep12961)) ≤ scalar12961.upperTail ∧
    exp (-((12961:ℝ)*em12961)) ≤ scalar12961.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12961:ℝ)) (by norm_num [ep12961]) ?_)
      (show bp12961^8 ≤ scalar12961.upperTail by norm_num [bp12961, scalar12961])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12961, bp12961, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12961:ℝ)) (by norm_num [em12961]) ?_)
      (show bm12961^8 ≤ scalar12961.lowerTail by norm_num [bm12961, scalar12961])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12961, bm12961, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12961 :
    agent12961.root+dsL+scalar12961.worldRadius < √(1/100/aL) ∧
    2*(agent12961.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12961, agent12961, scalar12961, tp12961, tm12961, ep12961, em12961, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12961, agent12961, scalar12961, tp12961, tm12961, ep12961, em12961, dsL]

noncomputable def master12961 : MasterCertificate 12961 world12961 agent12961 :=
  master scalar12961 dsL tp12961 tm12961 ep12961 em12961
    (by norm_num [dsL]) (by norm_num [tp12961]) (by norm_num [tm12961])
    (by norm_num [ep12961]) (by norm_num [em12961])
    positive12961 negative12961 tails12961.1 tails12961.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12961.1 tailGuards12961.2

theorem preserves12961 : master12961.toScalarCertificate = scalar12961 := rfl

noncomputable def tp12962 : ℝ := (2339592577 / 10000000000)
noncomputable def tm12962 : ℝ := (-((1528489947 / 2500000000)))
noncomputable def ep12962 : ℝ := (26053807656193521 / 50000000000000000000)
noncomputable def em12962 : ℝ := (50701835761793743 / 100000000000000000000)
noncomputable def bp12962 : ℝ := (42986948608494682679 / 100000000000000000000)
noncomputable def bm12962 : ℝ := (5497163051679648449 / 12500000000000000000)

theorem positive12962 :
    Eplus aL (agent12962.root+dsL) scalar12962.worldRadius world12962.frame
      agent12962.frame tp12962 ≤ -ep12962 := by
  apply positive_check (eT := (11566640579890634447 / 10000000000000000000)) (y := (38037993277124247291 / 100000000000000000000)) (u := (146284026482359447407 / 100000000000000000000))
  · norm_num [world12962, agent12962, scalar12962, tp12962, tm12962, ep12962, em12962, dsL]
  · norm_num [world12962, agent12962, scalar12962, tp12962, tm12962, ep12962, em12962, dsL]
  · norm_num [world12962, agent12962, scalar12962, tp12962, tm12962, ep12962, em12962, dsL]
  · norm_num [world12962, agent12962, scalar12962, tp12962, tm12962, ep12962, em12962, dsL]
  · norm_num [world12962, agent12962, scalar12962, tp12962, tm12962, ep12962, em12962, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12962, agent12962, tp12962, tm12962, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12962, agent12962, scalar12962, tp12962, tm12962, ep12962, em12962, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12962, agent12962, tp12962, tm12962, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12962, agent12962, scalar12962, tp12962, tm12962, ep12962, em12962, dsL]

theorem negative12962 :
    Eminus aL (agent12962.root+dsL) scalar12962.worldRadius world12962.frame
      agent12962.frame tm12962 ≤ -em12962 := by
  apply negative_check (lo := (68363321011680163427 / 100000000000000000000)) (hi := (17090830252920040857 / 25000000000000000000))
    (y := (-((71643454930636670419 / 100000000000000000000)))) (u := (24424542235652065441 / 50000000000000000000))
  · norm_num [world12962, agent12962, scalar12962, tp12962, tm12962, ep12962, em12962, dsL]
  · norm_num [world12962, agent12962, scalar12962, tp12962, tm12962, ep12962, em12962, dsL]
  · norm_num [world12962, agent12962, scalar12962, tp12962, tm12962, ep12962, em12962, dsL]
  · norm_num [world12962, agent12962, scalar12962, tp12962, tm12962, ep12962, em12962, dsL]
  · norm_num [world12962, agent12962, scalar12962, tp12962, tm12962, ep12962, em12962, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12962, agent12962, tp12962, tm12962, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12962, agent12962, tp12962, tm12962, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12962, agent12962, scalar12962, tp12962, tm12962, ep12962, em12962, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12962, agent12962, tp12962, tm12962, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12962, agent12962, scalar12962, tp12962, tm12962, ep12962, em12962, dsL]

theorem tails12962 :
    exp (-((12962:ℝ)*ep12962)) ≤ scalar12962.upperTail ∧
    exp (-((12962:ℝ)*em12962)) ≤ scalar12962.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12962:ℝ)) (by norm_num [ep12962]) ?_)
      (show bp12962^8 ≤ scalar12962.upperTail by norm_num [bp12962, scalar12962])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12962, bp12962, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12962:ℝ)) (by norm_num [em12962]) ?_)
      (show bm12962^8 ≤ scalar12962.lowerTail by norm_num [bm12962, scalar12962])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12962, bm12962, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12962 :
    agent12962.root+dsL+scalar12962.worldRadius < √(1/100/aL) ∧
    2*(agent12962.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12962, agent12962, scalar12962, tp12962, tm12962, ep12962, em12962, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12962, agent12962, scalar12962, tp12962, tm12962, ep12962, em12962, dsL]

noncomputable def master12962 : MasterCertificate 12962 world12962 agent12962 :=
  master scalar12962 dsL tp12962 tm12962 ep12962 em12962
    (by norm_num [dsL]) (by norm_num [tp12962]) (by norm_num [tm12962])
    (by norm_num [ep12962]) (by norm_num [em12962])
    positive12962 negative12962 tails12962.1 tails12962.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12962.1 tailGuards12962.2

theorem preserves12962 : master12962.toScalarCertificate = scalar12962 := rfl

noncomputable def tp12963 : ℝ := (1169834611 / 5000000000)
noncomputable def tm12963 : ℝ := (-((764265347 / 1250000000)))
noncomputable def ep12963 : ℝ := (10421986785923449 / 20000000000000000000)
noncomputable def em12963 : ℝ := (50703808779586963 / 100000000000000000000)
noncomputable def bp12963 : ℝ := (21491266934342086663 / 50000000000000000000)
noncomputable def bm12963 : ℝ := (43973111483704673247 / 100000000000000000000)

theorem positive12963 :
    Eplus aL (agent12963.root+dsL) scalar12963.worldRadius world12963.frame
      agent12963.frame tp12963 ≤ -ep12963 := by
  apply positive_check (eT := (23133319583881818383 / 20000000000000000000)) (y := (19019346246237119773 / 50000000000000000000)) (u := (146285049326303135563 / 100000000000000000000))
  · norm_num [world12963, agent12963, scalar12963, tp12963, tm12963, ep12963, em12963, dsL]
  · norm_num [world12963, agent12963, scalar12963, tp12963, tm12963, ep12963, em12963, dsL]
  · norm_num [world12963, agent12963, scalar12963, tp12963, tm12963, ep12963, em12963, dsL]
  · norm_num [world12963, agent12963, scalar12963, tp12963, tm12963, ep12963, em12963, dsL]
  · norm_num [world12963, agent12963, scalar12963, tp12963, tm12963, ep12963, em12963, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12963, agent12963, tp12963, tm12963, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12963, agent12963, scalar12963, tp12963, tm12963, ep12963, em12963, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12963, agent12963, tp12963, tm12963, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12963, agent12963, scalar12963, tp12963, tm12963, ep12963, em12963, dsL]

theorem negative12963 :
    Eminus aL (agent12963.root+dsL) scalar12963.worldRadius world12963.frame
      agent12963.frame tm12963 ≤ -em12963 := by
  apply negative_check (lo := (17090795729876817653 / 25000000000000000000)) (hi := (68363182919507270613 / 100000000000000000000))
    (y := (-((71643421908891392041 / 100000000000000000000)))) (u := (12212275150531759789 / 25000000000000000000))
  · norm_num [world12963, agent12963, scalar12963, tp12963, tm12963, ep12963, em12963, dsL]
  · norm_num [world12963, agent12963, scalar12963, tp12963, tm12963, ep12963, em12963, dsL]
  · norm_num [world12963, agent12963, scalar12963, tp12963, tm12963, ep12963, em12963, dsL]
  · norm_num [world12963, agent12963, scalar12963, tp12963, tm12963, ep12963, em12963, dsL]
  · norm_num [world12963, agent12963, scalar12963, tp12963, tm12963, ep12963, em12963, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12963, agent12963, tp12963, tm12963, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12963, agent12963, tp12963, tm12963, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12963, agent12963, scalar12963, tp12963, tm12963, ep12963, em12963, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12963, agent12963, tp12963, tm12963, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12963, agent12963, scalar12963, tp12963, tm12963, ep12963, em12963, dsL]

theorem tails12963 :
    exp (-((12963:ℝ)*ep12963)) ≤ scalar12963.upperTail ∧
    exp (-((12963:ℝ)*em12963)) ≤ scalar12963.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12963:ℝ)) (by norm_num [ep12963]) ?_)
      (show bp12963^8 ≤ scalar12963.upperTail by norm_num [bp12963, scalar12963])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12963, bp12963, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12963:ℝ)) (by norm_num [em12963]) ?_)
      (show bm12963^8 ≤ scalar12963.lowerTail by norm_num [bm12963, scalar12963])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12963, bm12963, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12963 :
    agent12963.root+dsL+scalar12963.worldRadius < √(1/100/aL) ∧
    2*(agent12963.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12963, agent12963, scalar12963, tp12963, tm12963, ep12963, em12963, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12963, agent12963, scalar12963, tp12963, tm12963, ep12963, em12963, dsL]

noncomputable def master12963 : MasterCertificate 12963 world12963 agent12963 :=
  master scalar12963 dsL tp12963 tm12963 ep12963 em12963
    (by norm_num [dsL]) (by norm_num [tp12963]) (by norm_num [tm12963])
    (by norm_num [ep12963]) (by norm_num [em12963])
    positive12963 negative12963 tails12963.1 tails12963.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12963.1 tailGuards12963.2

theorem preserves12963 : master12963.toScalarCertificate = scalar12963 := rfl

noncomputable def tp12964 : ℝ := (1169872911 / 5000000000)
noncomputable def tm12964 : ℝ := (-((3057142933 / 5000000000)))
noncomputable def ep12964 : ℝ := (52112251169125273 / 100000000000000000000)
noncomputable def em12964 : ℝ := (25352890247405901 / 50000000000000000000)
noncomputable def bp12964 : ℝ := (42978120292669867713 / 100000000000000000000)
noncomputable def bm12964 : ℝ := (21984459832480706209 / 50000000000000000000)

theorem positive12964 :
    Eplus aL (agent12964.root+dsL) scalar12964.worldRadius world12964.frame
      agent12964.frame tp12964 ≤ -ep12964 := by
  apply positive_check (eT := (115666789749174063819 / 100000000000000000000)) (y := (19019695752220836923 / 50000000000000000000)) (u := (146286071879878375359 / 100000000000000000000))
  · norm_num [world12964, agent12964, scalar12964, tp12964, tm12964, ep12964, em12964, dsL]
  · norm_num [world12964, agent12964, scalar12964, tp12964, tm12964, ep12964, em12964, dsL]
  · norm_num [world12964, agent12964, scalar12964, tp12964, tm12964, ep12964, em12964, dsL]
  · norm_num [world12964, agent12964, scalar12964, tp12964, tm12964, ep12964, em12964, dsL]
  · norm_num [world12964, agent12964, scalar12964, tp12964, tm12964, ep12964, em12964, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12964, agent12964, tp12964, tm12964, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12964, agent12964, scalar12964, tp12964, tm12964, ep12964, em12964, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12964, agent12964, tp12964, tm12964, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12964, agent12964, scalar12964, tp12964, tm12964, ep12964, em12964, dsL]

theorem negative12964 :
    Eminus aL (agent12964.root+dsL) scalar12964.worldRadius world12964.frame
      agent12964.frame tm12964 ≤ -em12964 := by
  apply negative_check (lo := (683630443365495319 / 1000000000000000000)) (hi := (68363044336549531901 / 100000000000000000000))
    (y := (-((71643390928863755703 / 100000000000000000000)))) (u := (48849115735594249973 / 100000000000000000000))
  · norm_num [world12964, agent12964, scalar12964, tp12964, tm12964, ep12964, em12964, dsL]
  · norm_num [world12964, agent12964, scalar12964, tp12964, tm12964, ep12964, em12964, dsL]
  · norm_num [world12964, agent12964, scalar12964, tp12964, tm12964, ep12964, em12964, dsL]
  · norm_num [world12964, agent12964, scalar12964, tp12964, tm12964, ep12964, em12964, dsL]
  · norm_num [world12964, agent12964, scalar12964, tp12964, tm12964, ep12964, em12964, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12964, agent12964, tp12964, tm12964, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12964, agent12964, tp12964, tm12964, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12964, agent12964, scalar12964, tp12964, tm12964, ep12964, em12964, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12964, agent12964, tp12964, tm12964, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12964, agent12964, scalar12964, tp12964, tm12964, ep12964, em12964, dsL]

theorem tails12964 :
    exp (-((12964:ℝ)*ep12964)) ≤ scalar12964.upperTail ∧
    exp (-((12964:ℝ)*em12964)) ≤ scalar12964.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12964:ℝ)) (by norm_num [ep12964]) ?_)
      (show bp12964^8 ≤ scalar12964.upperTail by norm_num [bp12964, scalar12964])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12964, bp12964, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12964:ℝ)) (by norm_num [em12964]) ?_)
      (show bm12964^8 ≤ scalar12964.lowerTail by norm_num [bm12964, scalar12964])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12964, bm12964, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12964 :
    agent12964.root+dsL+scalar12964.worldRadius < √(1/100/aL) ∧
    2*(agent12964.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12964, agent12964, scalar12964, tp12964, tm12964, ep12964, em12964, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12964, agent12964, scalar12964, tp12964, tm12964, ep12964, em12964, dsL]

noncomputable def master12964 : MasterCertificate 12964 world12964 agent12964 :=
  master scalar12964 dsL tp12964 tm12964 ep12964 em12964
    (by norm_num [dsL]) (by norm_num [tp12964]) (by norm_num [tm12964])
    (by norm_num [ep12964]) (by norm_num [em12964])
    positive12964 negative12964 tails12964.1 tails12964.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12964.1 tailGuards12964.2

theorem preserves12964 : master12964.toScalarCertificate = scalar12964 := rfl

noncomputable def tp12965 : ℝ := (1169911179 / 5000000000)
noncomputable def tm12965 : ℝ := (-((6114448629 / 10000000000)))
noncomputable def ep12965 : ℝ := (52114566989859987 / 100000000000000000000)
noncomputable def em12965 : ℝ := (12676937729925691 / 25000000000000000000)
noncomputable def bp12965 : ℝ := (42973707908998149349 / 100000000000000000000)
noncomputable def bm12965 : ℝ := (43964728948463520223 / 100000000000000000000)

theorem positive12965 :
    Eplus aL (agent12965.root+dsL) scalar12965.worldRadius world12965.frame
      agent12965.frame tp12965 ≤ -ep12965 := by
  apply positive_check (eT := (115666981151496185513 / 100000000000000000000)) (y := (38040089573703586279 / 100000000000000000000)) (u := (18285886632693112679 / 12500000000000000000))
  · norm_num [world12965, agent12965, scalar12965, tp12965, tm12965, ep12965, em12965, dsL]
  · norm_num [world12965, agent12965, scalar12965, tp12965, tm12965, ep12965, em12965, dsL]
  · norm_num [world12965, agent12965, scalar12965, tp12965, tm12965, ep12965, em12965, dsL]
  · norm_num [world12965, agent12965, scalar12965, tp12965, tm12965, ep12965, em12965, dsL]
  · norm_num [world12965, agent12965, scalar12965, tp12965, tm12965, ep12965, em12965, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12965, agent12965, tp12965, tm12965, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12965, agent12965, scalar12965, tp12965, tm12965, ep12965, em12965, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12965, agent12965, tp12965, tm12965, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12965, agent12965, scalar12965, tp12965, tm12965, ep12965, em12965, dsL]

theorem negative12965 :
    Eminus aL (agent12965.root+dsL) scalar12965.worldRadius world12965.frame
      agent12965.frame tm12965 ≤ -em12965 := by
  apply negative_check (lo := (13672581417431172873 / 20000000000000000000)) (hi := (34181453543577932183 / 50000000000000000000))
    (y := (-((1791083921782676773 / 2500000000000000000)))) (u := (9769826474482472937 / 20000000000000000000))
  · norm_num [world12965, agent12965, scalar12965, tp12965, tm12965, ep12965, em12965, dsL]
  · norm_num [world12965, agent12965, scalar12965, tp12965, tm12965, ep12965, em12965, dsL]
  · norm_num [world12965, agent12965, scalar12965, tp12965, tm12965, ep12965, em12965, dsL]
  · norm_num [world12965, agent12965, scalar12965, tp12965, tm12965, ep12965, em12965, dsL]
  · norm_num [world12965, agent12965, scalar12965, tp12965, tm12965, ep12965, em12965, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12965, agent12965, tp12965, tm12965, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12965, agent12965, tp12965, tm12965, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12965, agent12965, scalar12965, tp12965, tm12965, ep12965, em12965, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12965, agent12965, tp12965, tm12965, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12965, agent12965, scalar12965, tp12965, tm12965, ep12965, em12965, dsL]

theorem tails12965 :
    exp (-((12965:ℝ)*ep12965)) ≤ scalar12965.upperTail ∧
    exp (-((12965:ℝ)*em12965)) ≤ scalar12965.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12965:ℝ)) (by norm_num [ep12965]) ?_)
      (show bp12965^8 ≤ scalar12965.upperTail by norm_num [bp12965, scalar12965])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12965, bp12965, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12965:ℝ)) (by norm_num [em12965]) ?_)
      (show bm12965^8 ≤ scalar12965.lowerTail by norm_num [bm12965, scalar12965])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12965, bm12965, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12965 :
    agent12965.root+dsL+scalar12965.worldRadius < √(1/100/aL) ∧
    2*(agent12965.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12965, agent12965, scalar12965, tp12965, tm12965, ep12965, em12965, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12965, agent12965, scalar12965, tp12965, tm12965, ep12965, em12965, dsL]

noncomputable def master12965 : MasterCertificate 12965 world12965 agent12965 :=
  master scalar12965 dsL tp12965 tm12965 ep12965 em12965
    (by norm_num [dsL]) (by norm_num [tp12965]) (by norm_num [tm12965])
    (by norm_num [ep12965]) (by norm_num [em12965])
    positive12965 negative12965 tails12965.1 tails12965.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12965.1 tailGuards12965.2

theorem preserves12965 : master12965.toScalarCertificate = scalar12965 := rfl

noncomputable def tp12966 : ℝ := (2339898937 / 10000000000)
noncomputable def tm12966 : ℝ := (-((305730571 / 500000000)))
noncomputable def ep12966 : ℝ := (52116881751676549 / 100000000000000000000)
noncomputable def em12966 : ℝ := (50709720376742127 / 100000000000000000000)
noncomputable def bp12966 : ℝ := (42969296467011355923 / 100000000000000000000)
noncomputable def bm12966 : ℝ := (43960539104419167649 / 100000000000000000000)

theorem positive12966 :
    Eplus aL (agent12966.root+dsL) scalar12966.worldRadius world12966.frame
      agent12966.frame tp12966 ≤ -ep12966 := by
  apply positive_check (eT := (2313343457924376929 / 2000000000000000000)) (y := (19020394387120574697 / 50000000000000000000)) (u := (5851524636210473337 / 4000000000000000000))
  · norm_num [world12966, agent12966, scalar12966, tp12966, tm12966, ep12966, em12966, dsL]
  · norm_num [world12966, agent12966, scalar12966, tp12966, tm12966, ep12966, em12966, dsL]
  · norm_num [world12966, agent12966, scalar12966, tp12966, tm12966, ep12966, em12966, dsL]
  · norm_num [world12966, agent12966, scalar12966, tp12966, tm12966, ep12966, em12966, dsL]
  · norm_num [world12966, agent12966, scalar12966, tp12966, tm12966, ep12966, em12966, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12966, agent12966, tp12966, tm12966, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12966, agent12966, scalar12966, tp12966, tm12966, ep12966, em12966, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12966, agent12966, tp12966, tm12966, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12966, agent12966, scalar12966, tp12966, tm12966, ep12966, em12966, dsL]

theorem negative12966 :
    Eminus aL (agent12966.root+dsL) scalar12966.worldRadius world12966.frame
      agent12966.frame tm12966 ≤ -em12966 := by
  apply negative_check (lo := (68362769661694213397 / 100000000000000000000)) (hi := (34181384830847106699 / 50000000000000000000))
    (y := (-((71643323980382366209 / 100000000000000000000)))) (u := (48849148439346354481 / 100000000000000000000))
  · norm_num [world12966, agent12966, scalar12966, tp12966, tm12966, ep12966, em12966, dsL]
  · norm_num [world12966, agent12966, scalar12966, tp12966, tm12966, ep12966, em12966, dsL]
  · norm_num [world12966, agent12966, scalar12966, tp12966, tm12966, ep12966, em12966, dsL]
  · norm_num [world12966, agent12966, scalar12966, tp12966, tm12966, ep12966, em12966, dsL]
  · norm_num [world12966, agent12966, scalar12966, tp12966, tm12966, ep12966, em12966, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12966, agent12966, tp12966, tm12966, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12966, agent12966, tp12966, tm12966, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12966, agent12966, scalar12966, tp12966, tm12966, ep12966, em12966, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12966, agent12966, tp12966, tm12966, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12966, agent12966, scalar12966, tp12966, tm12966, ep12966, em12966, dsL]

theorem tails12966 :
    exp (-((12966:ℝ)*ep12966)) ≤ scalar12966.upperTail ∧
    exp (-((12966:ℝ)*em12966)) ≤ scalar12966.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12966:ℝ)) (by norm_num [ep12966]) ?_)
      (show bp12966^8 ≤ scalar12966.upperTail by norm_num [bp12966, scalar12966])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12966, bp12966, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12966:ℝ)) (by norm_num [em12966]) ?_)
      (show bm12966^8 ≤ scalar12966.lowerTail by norm_num [bm12966, scalar12966])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12966, bm12966, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12966 :
    agent12966.root+dsL+scalar12966.worldRadius < √(1/100/aL) ∧
    2*(agent12966.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12966, agent12966, scalar12966, tp12966, tm12966, ep12966, em12966, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12966, agent12966, scalar12966, tp12966, tm12966, ep12966, em12966, dsL]

noncomputable def master12966 : MasterCertificate 12966 world12966 agent12966 :=
  master scalar12966 dsL tp12966 tm12966 ep12966 em12966
    (by norm_num [dsL]) (by norm_num [tp12966]) (by norm_num [tm12966])
    (by norm_num [ep12966]) (by norm_num [em12966])
    positive12966 negative12966 tails12966.1 tails12966.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12966.1 tailGuards12966.2

theorem preserves12966 : master12966.toScalarCertificate = scalar12966 := rfl

noncomputable def tp12967 : ℝ := (467995081 / 2000000000)
noncomputable def tm12967 : ℝ := (-((3057387049 / 5000000000)))
noncomputable def ep12967 : ℝ := (26059597554442301 / 50000000000000000000)
noncomputable def em12967 : ℝ := (633896106255281 / 1250000000000000000)
noncomputable def bp12967 : ℝ := (10741221551856078051 / 25000000000000000000)
noncomputable def bm12967 : ℝ := (21978175196615193017 / 50000000000000000000)

theorem positive12967 :
    Eplus aL (agent12967.root+dsL) scalar12967.worldRadius world12967.frame
      agent12967.frame tp12967 ≤ -ep12967 := by
  apply positive_check (eT := (28916840968840182991 / 25000000000000000000)) (y := (7608297303230281647 / 20000000000000000000)) (u := (29257827324463442733 / 20000000000000000000))
  · norm_num [world12967, agent12967, scalar12967, tp12967, tm12967, ep12967, em12967, dsL]
  · norm_num [world12967, agent12967, scalar12967, tp12967, tm12967, ep12967, em12967, dsL]
  · norm_num [world12967, agent12967, scalar12967, tp12967, tm12967, ep12967, em12967, dsL]
  · norm_num [world12967, agent12967, scalar12967, tp12967, tm12967, ep12967, em12967, dsL]
  · norm_num [world12967, agent12967, scalar12967, tp12967, tm12967, ep12967, em12967, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12967, agent12967, tp12967, tm12967, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12967, agent12967, scalar12967, tp12967, tm12967, ep12967, em12967, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12967, agent12967, tp12967, tm12967, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12967, agent12967, scalar12967, tp12967, tm12967, ep12967, em12967, dsL]

theorem negative12967 :
    Eminus aL (agent12967.root+dsL) scalar12967.worldRadius world12967.frame
      agent12967.frame tm12967 ≤ -em12967 := by
  apply negative_check (lo := (4272664541232997589 / 6250000000000000000)) (hi := (2734505306389118457 / 4000000000000000000))
    (y := (-((71643290648828043579 / 100000000000000000000)))) (u := (12212291180382379059 / 25000000000000000000))
  · norm_num [world12967, agent12967, scalar12967, tp12967, tm12967, ep12967, em12967, dsL]
  · norm_num [world12967, agent12967, scalar12967, tp12967, tm12967, ep12967, em12967, dsL]
  · norm_num [world12967, agent12967, scalar12967, tp12967, tm12967, ep12967, em12967, dsL]
  · norm_num [world12967, agent12967, scalar12967, tp12967, tm12967, ep12967, em12967, dsL]
  · norm_num [world12967, agent12967, scalar12967, tp12967, tm12967, ep12967, em12967, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12967, agent12967, tp12967, tm12967, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12967, agent12967, tp12967, tm12967, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12967, agent12967, scalar12967, tp12967, tm12967, ep12967, em12967, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12967, agent12967, tp12967, tm12967, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12967, agent12967, scalar12967, tp12967, tm12967, ep12967, em12967, dsL]

theorem tails12967 :
    exp (-((12967:ℝ)*ep12967)) ≤ scalar12967.upperTail ∧
    exp (-((12967:ℝ)*em12967)) ≤ scalar12967.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12967:ℝ)) (by norm_num [ep12967]) ?_)
      (show bp12967^8 ≤ scalar12967.upperTail by norm_num [bp12967, scalar12967])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12967, bp12967, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12967:ℝ)) (by norm_num [em12967]) ?_)
      (show bm12967^8 ≤ scalar12967.lowerTail by norm_num [bm12967, scalar12967])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12967, bm12967, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12967 :
    agent12967.root+dsL+scalar12967.worldRadius < √(1/100/aL) ∧
    2*(agent12967.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12967, agent12967, scalar12967, tp12967, tm12967, ep12967, em12967, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12967, agent12967, scalar12967, tp12967, tm12967, ep12967, em12967, dsL]

noncomputable def master12967 : MasterCertificate 12967 world12967 agent12967 :=
  master scalar12967 dsL tp12967 tm12967 ep12967 em12967
    (by norm_num [dsL]) (by norm_num [tp12967]) (by norm_num [tm12967])
    (by norm_num [ep12967]) (by norm_num [em12967])
    positive12967 negative12967 tails12967.1 tails12967.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12967.1 tailGuards12967.2

theorem preserves12967 : master12967.toScalarCertificate = scalar12967 := rfl

noncomputable def tp12968 : ℝ := (1170025929 / 5000000000)
noncomputable def tm12968 : ℝ := (-((3057468337 / 5000000000)))
noncomputable def ep12968 : ℝ := (3257594240758451 / 6250000000000000000)
noncomputable def em12968 : ℝ := (50713656062863001 / 100000000000000000000)
noncomputable def bp12968 : ℝ := (42960476579591210753 / 100000000000000000000)
noncomputable def bm12968 : ℝ := (43952162264761652219 / 100000000000000000000)

theorem positive12968 :
    Eplus aL (agent12968.root+dsL) scalar12968.worldRadius world12968.frame
      agent12968.frame tp12968 ≤ -ep12968 := by
  apply positive_check (eT := (57833777389794374739 / 50000000000000000000)) (y := (19021092112326718769 / 50000000000000000000)) (u := (146290157297621637883 / 100000000000000000000))
  · norm_num [world12968, agent12968, scalar12968, tp12968, tm12968, ep12968, em12968, dsL]
  · norm_num [world12968, agent12968, scalar12968, tp12968, tm12968, ep12968, em12968, dsL]
  · norm_num [world12968, agent12968, scalar12968, tp12968, tm12968, ep12968, em12968, dsL]
  · norm_num [world12968, agent12968, scalar12968, tp12968, tm12968, ep12968, em12968, dsL]
  · norm_num [world12968, agent12968, scalar12968, tp12968, tm12968, ep12968, em12968, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12968, agent12968, tp12968, tm12968, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12968, agent12968, scalar12968, tp12968, tm12968, ep12968, em12968, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12968, agent12968, tp12968, tm12968, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12968, agent12968, scalar12968, tp12968, tm12968, ep12968, em12968, dsL]

theorem negative12968 :
    Eminus aL (agent12968.root+dsL) scalar12968.worldRadius world12968.frame
      agent12968.frame tm12968 ≤ -em12968 := by
  apply negative_check (lo := (68362496034527264499 / 100000000000000000000)) (hi := (136724992069054529 / 200000000000000000))
    (y := (-((14328651389639275623 / 20000000000000000000)))) (u := (1953967247360374587 / 4000000000000000000))
  · norm_num [world12968, agent12968, scalar12968, tp12968, tm12968, ep12968, em12968, dsL]
  · norm_num [world12968, agent12968, scalar12968, tp12968, tm12968, ep12968, em12968, dsL]
  · norm_num [world12968, agent12968, scalar12968, tp12968, tm12968, ep12968, em12968, dsL]
  · norm_num [world12968, agent12968, scalar12968, tp12968, tm12968, ep12968, em12968, dsL]
  · norm_num [world12968, agent12968, scalar12968, tp12968, tm12968, ep12968, em12968, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12968, agent12968, tp12968, tm12968, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12968, agent12968, tp12968, tm12968, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12968, agent12968, scalar12968, tp12968, tm12968, ep12968, em12968, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12968, agent12968, tp12968, tm12968, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12968, agent12968, scalar12968, tp12968, tm12968, ep12968, em12968, dsL]

theorem tails12968 :
    exp (-((12968:ℝ)*ep12968)) ≤ scalar12968.upperTail ∧
    exp (-((12968:ℝ)*em12968)) ≤ scalar12968.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12968:ℝ)) (by norm_num [ep12968]) ?_)
      (show bp12968^8 ≤ scalar12968.upperTail by norm_num [bp12968, scalar12968])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12968, bp12968, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12968:ℝ)) (by norm_num [em12968]) ?_)
      (show bm12968^8 ≤ scalar12968.lowerTail by norm_num [bm12968, scalar12968])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12968, bm12968, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12968 :
    agent12968.root+dsL+scalar12968.worldRadius < √(1/100/aL) ∧
    2*(agent12968.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12968, agent12968, scalar12968, tp12968, tm12968, ep12968, em12968, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12968, agent12968, scalar12968, tp12968, tm12968, ep12968, em12968, dsL]

noncomputable def master12968 : MasterCertificate 12968 world12968 agent12968 :=
  master scalar12968 dsL tp12968 tm12968 ep12968 em12968
    (by norm_num [dsL]) (by norm_num [tp12968]) (by norm_num [tm12968])
    (by norm_num [ep12968]) (by norm_num [em12968])
    positive12968 negative12968 tails12968.1 tails12968.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12968.1 tailGuards12968.2

theorem preserves12968 : master12968.toScalarCertificate = scalar12968 := rfl

noncomputable def tp12969 : ℝ := (2340128279 / 10000000000)
noncomputable def tm12969 : ℝ := (-((3057549571 / 5000000000)))
noncomputable def ep12969 : ℝ := (52123819033110027 / 100000000000000000000)
noncomputable def em12969 : ℝ := (12678905546326287 / 25000000000000000000)
noncomputable def bp12969 : ℝ := (83898570788850161 / 195312500000000000)
noncomputable def bm12969 : ℝ := (43947975345087889191 / 100000000000000000000)

theorem positive12969 :
    Eplus aL (agent12969.root+dsL) scalar12969.worldRadius world12969.frame
      agent12969.frame tp12969 ≤ -ep12969 := by
  apply positive_check (eT := (57833872743332826083 / 50000000000000000000)) (y := (7608576340235623377 / 20000000000000000000)) (u := (146291177640685027817 / 100000000000000000000))
  · norm_num [world12969, agent12969, scalar12969, tp12969, tm12969, ep12969, em12969, dsL]
  · norm_num [world12969, agent12969, scalar12969, tp12969, tm12969, ep12969, em12969, dsL]
  · norm_num [world12969, agent12969, scalar12969, tp12969, tm12969, ep12969, em12969, dsL]
  · norm_num [world12969, agent12969, scalar12969, tp12969, tm12969, ep12969, em12969, dsL]
  · norm_num [world12969, agent12969, scalar12969, tp12969, tm12969, ep12969, em12969, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12969, agent12969, tp12969, tm12969, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12969, agent12969, scalar12969, tp12969, tm12969, ep12969, em12969, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12969, agent12969, tp12969, tm12969, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12969, agent12969, scalar12969, tp12969, tm12969, ep12969, em12969, dsL]

theorem negative12969 :
    Eminus aL (agent12969.root+dsL) scalar12969.worldRadius world12969.frame
      agent12969.frame tm12969 ≤ -em12969 := by
  apply negative_check (lo := (34181179905741825789 / 50000000000000000000)) (hi := (68362359811483651579 / 100000000000000000000))
    (y := (-((71643222564733358047 / 100000000000000000000)))) (u := (9769839596010480043 / 20000000000000000000))
  · norm_num [world12969, agent12969, scalar12969, tp12969, tm12969, ep12969, em12969, dsL]
  · norm_num [world12969, agent12969, scalar12969, tp12969, tm12969, ep12969, em12969, dsL]
  · norm_num [world12969, agent12969, scalar12969, tp12969, tm12969, ep12969, em12969, dsL]
  · norm_num [world12969, agent12969, scalar12969, tp12969, tm12969, ep12969, em12969, dsL]
  · norm_num [world12969, agent12969, scalar12969, tp12969, tm12969, ep12969, em12969, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12969, agent12969, tp12969, tm12969, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12969, agent12969, tp12969, tm12969, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12969, agent12969, scalar12969, tp12969, tm12969, ep12969, em12969, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12969, agent12969, tp12969, tm12969, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12969, agent12969, scalar12969, tp12969, tm12969, ep12969, em12969, dsL]

theorem tails12969 :
    exp (-((12969:ℝ)*ep12969)) ≤ scalar12969.upperTail ∧
    exp (-((12969:ℝ)*em12969)) ≤ scalar12969.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12969:ℝ)) (by norm_num [ep12969]) ?_)
      (show bp12969^8 ≤ scalar12969.upperTail by norm_num [bp12969, scalar12969])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12969, bp12969, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12969:ℝ)) (by norm_num [em12969]) ?_)
      (show bm12969^8 ≤ scalar12969.lowerTail by norm_num [bm12969, scalar12969])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12969, bm12969, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12969 :
    agent12969.root+dsL+scalar12969.worldRadius < √(1/100/aL) ∧
    2*(agent12969.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12969, agent12969, scalar12969, tp12969, tm12969, ep12969, em12969, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12969, agent12969, scalar12969, tp12969, tm12969, ep12969, em12969, dsL]

noncomputable def master12969 : MasterCertificate 12969 world12969 agent12969 :=
  master scalar12969 dsL tp12969 tm12969 ep12969 em12969
    (by norm_num [dsL]) (by norm_num [tp12969]) (by norm_num [tm12969])
    (by norm_num [ep12969]) (by norm_num [em12969])
    positive12969 negative12969 tails12969.1 tails12969.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12969.1 tailGuards12969.2

theorem preserves12969 : master12969.toScalarCertificate = scalar12969 := rfl

noncomputable def tp12970 : ℝ := (2340276769 / 10000000000)
noncomputable def tm12970 : ℝ := (-((3057739889 / 5000000000)))
noncomputable def ep12970 : ℝ := (52127494928808657 / 100000000000000000000)
noncomputable def em12970 : ℝ := (25359538819990547 / 50000000000000000000)
noncomputable def bp12970 : ℝ := (42950709798618048153 / 100000000000000000000)
noncomputable def bm12970 : ℝ := (8788545512639267167 / 20000000000000000000)

theorem positive12970 :
    Eplus aL (agent12970.root+dsL) scalar12970.worldRadius world12970.frame
      agent12970.frame tp12970 ≤ -ep12970 := by
  apply positive_check (eT := (57834227352549955547 / 50000000000000000000)) (y := (4755357852610439877 / 12500000000000000000)) (u := (2285799219070036343 / 1562500000000000000))
  · norm_num [world12970, agent12970, scalar12970, tp12970, tm12970, ep12970, em12970, dsL]
  · norm_num [world12970, agent12970, scalar12970, tp12970, tm12970, ep12970, em12970, dsL]
  · norm_num [world12970, agent12970, scalar12970, tp12970, tm12970, ep12970, em12970, dsL]
  · norm_num [world12970, agent12970, scalar12970, tp12970, tm12970, ep12970, em12970, dsL]
  · norm_num [world12970, agent12970, scalar12970, tp12970, tm12970, ep12970, em12970, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12970, agent12970, tp12970, tm12970, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12970, agent12970, scalar12970, tp12970, tm12970, ep12970, em12970, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12970, agent12970, tp12970, tm12970, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12970, agent12970, scalar12970, tp12970, tm12970, ep12970, em12970, dsL]

theorem negative12970 :
    Eminus aL (agent12970.root+dsL) scalar12970.worldRadius world12970.frame
      agent12970.frame tm12970 ≤ -em12970 := by
  apply negative_check (lo := (8545161988306478003 / 12500000000000000000)) (hi := (2734451836258072961 / 4000000000000000000))
    (y := (-((14328262685504430111 / 20000000000000000000)))) (u := (48850130587170760253 / 100000000000000000000))
  · norm_num [world12970, agent12970, scalar12970, tp12970, tm12970, ep12970, em12970, dsL]
  · norm_num [world12970, agent12970, scalar12970, tp12970, tm12970, ep12970, em12970, dsL]
  · norm_num [world12970, agent12970, scalar12970, tp12970, tm12970, ep12970, em12970, dsL]
  · norm_num [world12970, agent12970, scalar12970, tp12970, tm12970, ep12970, em12970, dsL]
  · norm_num [world12970, agent12970, scalar12970, tp12970, tm12970, ep12970, em12970, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12970, agent12970, tp12970, tm12970, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12970, agent12970, tp12970, tm12970, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12970, agent12970, scalar12970, tp12970, tm12970, ep12970, em12970, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12970, agent12970, tp12970, tm12970, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12970, agent12970, scalar12970, tp12970, tm12970, ep12970, em12970, dsL]

theorem tails12970 :
    exp (-((12970:ℝ)*ep12970)) ≤ scalar12970.upperTail ∧
    exp (-((12970:ℝ)*em12970)) ≤ scalar12970.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12970:ℝ)) (by norm_num [ep12970]) ?_)
      (show bp12970^8 ≤ scalar12970.upperTail by norm_num [bp12970, scalar12970])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12970, bp12970, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12970:ℝ)) (by norm_num [em12970]) ?_)
      (show bm12970^8 ≤ scalar12970.lowerTail by norm_num [bm12970, scalar12970])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12970, bm12970, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12970 :
    agent12970.root+dsL+scalar12970.worldRadius < √(1/100/aL) ∧
    2*(agent12970.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12970, agent12970, scalar12970, tp12970, tm12970, ep12970, em12970, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12970, agent12970, scalar12970, tp12970, tm12970, ep12970, em12970, dsL]

noncomputable def master12970 : MasterCertificate 12970 world12970 agent12970 :=
  master scalar12970 dsL tp12970 tm12970 ep12970 em12970
    (by norm_num [dsL]) (by norm_num [tp12970]) (by norm_num [tm12970])
    (by norm_num [ep12970]) (by norm_num [em12970])
    positive12970 negative12970 tails12970.1 tails12970.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12970.1 tailGuards12970.2

theorem preserves12970 : master12970.toScalarCertificate = scalar12970 := rfl

noncomputable def tp12971 : ℝ := (1170176557 / 5000000000)
noncomputable def tm12971 : ℝ := (-((152891053 / 250000000)))
noncomputable def ep12971 : ℝ := (10425960747119289 / 20000000000000000000)
noncomputable def em12971 : ℝ := (25360520773323339 / 50000000000000000000)
noncomputable def bp12971 : ℝ := (5368287943596792033 / 12500000000000000000)
noncomputable def bm12971 : ℝ := (439385426070766327 / 1000000000000000000)

theorem positive12971 :
    Eplus aL (agent12971.root+dsL) scalar12971.worldRadius world12971.frame
      agent12971.frame tp12971 ≤ -ep12971 := by
  apply positive_check (eT := (57834322460630428679 / 50000000000000000000)) (y := (38043559758404232253 / 100000000000000000000)) (u := (146292169581949150661 / 100000000000000000000))
  · norm_num [world12971, agent12971, scalar12971, tp12971, tm12971, ep12971, em12971, dsL]
  · norm_num [world12971, agent12971, scalar12971, tp12971, tm12971, ep12971, em12971, dsL]
  · norm_num [world12971, agent12971, scalar12971, tp12971, tm12971, ep12971, em12971, dsL]
  · norm_num [world12971, agent12971, scalar12971, tp12971, tm12971, ep12971, em12971, dsL]
  · norm_num [world12971, agent12971, scalar12971, tp12971, tm12971, ep12971, em12971, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12971, agent12971, tp12971, tm12971, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12971, agent12971, scalar12971, tp12971, tm12971, ep12971, em12971, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12971, agent12971, tp12971, tm12971, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12971, agent12971, scalar12971, tp12971, tm12971, ep12971, em12971, dsL]

theorem negative12971 :
    Eminus aL (agent12971.root+dsL) scalar12971.worldRadius world12971.frame
      agent12971.frame tm12971 ≤ -em12971 := by
  apply negative_check (lo := (68361160126785677189 / 100000000000000000000)) (hi := (6836116012678567719 / 10000000000000000000))
    (y := (-((5731302342653133 / 8000000000000000)))) (u := (24425073633368536567 / 50000000000000000000))
  · norm_num [world12971, agent12971, scalar12971, tp12971, tm12971, ep12971, em12971, dsL]
  · norm_num [world12971, agent12971, scalar12971, tp12971, tm12971, ep12971, em12971, dsL]
  · norm_num [world12971, agent12971, scalar12971, tp12971, tm12971, ep12971, em12971, dsL]
  · norm_num [world12971, agent12971, scalar12971, tp12971, tm12971, ep12971, em12971, dsL]
  · norm_num [world12971, agent12971, scalar12971, tp12971, tm12971, ep12971, em12971, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12971, agent12971, tp12971, tm12971, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12971, agent12971, tp12971, tm12971, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12971, agent12971, scalar12971, tp12971, tm12971, ep12971, em12971, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12971, agent12971, tp12971, tm12971, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12971, agent12971, scalar12971, tp12971, tm12971, ep12971, em12971, dsL]

theorem tails12971 :
    exp (-((12971:ℝ)*ep12971)) ≤ scalar12971.upperTail ∧
    exp (-((12971:ℝ)*em12971)) ≤ scalar12971.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12971:ℝ)) (by norm_num [ep12971]) ?_)
      (show bp12971^8 ≤ scalar12971.upperTail by norm_num [bp12971, scalar12971])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12971, bp12971, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12971:ℝ)) (by norm_num [em12971]) ?_)
      (show bm12971^8 ≤ scalar12971.lowerTail by norm_num [bm12971, scalar12971])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12971, bm12971, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12971 :
    agent12971.root+dsL+scalar12971.worldRadius < √(1/100/aL) ∧
    2*(agent12971.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12971, agent12971, scalar12971, tp12971, tm12971, ep12971, em12971, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12971, agent12971, scalar12971, tp12971, tm12971, ep12971, em12971, dsL]

noncomputable def master12971 : MasterCertificate 12971 world12971 agent12971 :=
  master scalar12971 dsL tp12971 tm12971 ep12971 em12971
    (by norm_num [dsL]) (by norm_num [tp12971]) (by norm_num [tm12971])
    (by norm_num [ep12971]) (by norm_num [em12971])
    positive12971 negative12971 tails12971.1 tails12971.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12971.1 tailGuards12971.2

theorem preserves12971 : master12971.toScalarCertificate = scalar12971 := rfl

noncomputable def tp12972 : ℝ := (1170214727 / 5000000000)
noncomputable def tm12972 : ℝ := (-((3057902161 / 5000000000)))
noncomputable def ep12972 : ℝ := (52132110822328383 / 100000000000000000000)
noncomputable def em12972 : ℝ := (50723003906589853 / 100000000000000000000)
noncomputable def bp12972 : ℝ := (42941898700779760477 / 100000000000000000000)
noncomputable def bm12972 : ℝ := (43934358935688761389 / 100000000000000000000)

theorem positive12972 :
    Eplus aL (agent12972.root+dsL) scalar12972.worldRadius world12972.frame
      agent12972.frame tp12972 ≤ -ep12972 := by
  apply positive_check (eT := (28917208783621867121 / 25000000000000000000)) (y := (38044256782087444187 / 100000000000000000000)) (u := (146293189276571573791 / 100000000000000000000))
  · norm_num [world12972, agent12972, scalar12972, tp12972, tm12972, ep12972, em12972, dsL]
  · norm_num [world12972, agent12972, scalar12972, tp12972, tm12972, ep12972, em12972, dsL]
  · norm_num [world12972, agent12972, scalar12972, tp12972, tm12972, ep12972, em12972, dsL]
  · norm_num [world12972, agent12972, scalar12972, tp12972, tm12972, ep12972, em12972, dsL]
  · norm_num [world12972, agent12972, scalar12972, tp12972, tm12972, ep12972, em12972, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12972, agent12972, tp12972, tm12972, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12972, agent12972, scalar12972, tp12972, tm12972, ep12972, em12972, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12972, agent12972, tp12972, tm12972, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12972, agent12972, scalar12972, tp12972, tm12972, ep12972, em12972, dsL]

theorem negative12972 :
    Eminus aL (agent12972.root+dsL) scalar12972.worldRadius world12972.frame
      agent12972.frame tm12972 ≤ -em12972 := by
  apply negative_check (lo := (13672204977069637001 / 20000000000000000000)) (hi := (34180512442674092503 / 50000000000000000000))
    (y := (-((1119394435274378437 / 1562500000000000000)))) (u := (24425082286099917237 / 50000000000000000000))
  · norm_num [world12972, agent12972, scalar12972, tp12972, tm12972, ep12972, em12972, dsL]
  · norm_num [world12972, agent12972, scalar12972, tp12972, tm12972, ep12972, em12972, dsL]
  · norm_num [world12972, agent12972, scalar12972, tp12972, tm12972, ep12972, em12972, dsL]
  · norm_num [world12972, agent12972, scalar12972, tp12972, tm12972, ep12972, em12972, dsL]
  · norm_num [world12972, agent12972, scalar12972, tp12972, tm12972, ep12972, em12972, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12972, agent12972, tp12972, tm12972, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12972, agent12972, tp12972, tm12972, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12972, agent12972, scalar12972, tp12972, tm12972, ep12972, em12972, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12972, agent12972, tp12972, tm12972, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12972, agent12972, scalar12972, tp12972, tm12972, ep12972, em12972, dsL]

theorem tails12972 :
    exp (-((12972:ℝ)*ep12972)) ≤ scalar12972.upperTail ∧
    exp (-((12972:ℝ)*em12972)) ≤ scalar12972.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12972:ℝ)) (by norm_num [ep12972]) ?_)
      (show bp12972^8 ≤ scalar12972.upperTail by norm_num [bp12972, scalar12972])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12972, bp12972, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12972:ℝ)) (by norm_num [em12972]) ?_)
      (show bm12972^8 ≤ scalar12972.lowerTail by norm_num [bm12972, scalar12972])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12972, bm12972, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12972 :
    agent12972.root+dsL+scalar12972.worldRadius < √(1/100/aL) ∧
    2*(agent12972.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12972, agent12972, scalar12972, tp12972, tm12972, ep12972, em12972, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12972, agent12972, scalar12972, tp12972, tm12972, ep12972, em12972, dsL]

noncomputable def master12972 : MasterCertificate 12972 world12972 agent12972 :=
  master scalar12972 dsL tp12972 tm12972 ep12972 em12972
    (by norm_num [dsL]) (by norm_num [tp12972]) (by norm_num [tm12972])
    (by norm_num [ep12972]) (by norm_num [em12972])
    positive12972 negative12972 tails12972.1 tails12972.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12972.1 tailGuards12972.2

theorem preserves12972 : master12972.toScalarCertificate = scalar12972 := rfl

noncomputable def tp12973 : ℝ := (73140803 / 312500000)
noncomputable def tm12973 : ℝ := (-((6115966553 / 10000000000)))
noncomputable def ep12973 : ℝ := (52134417934296153 / 100000000000000000000)
noncomputable def em12973 : ℝ := (50724966257856137 / 100000000000000000000)
noncomputable def bp12973 : ℝ := (536718675491899609 / 1250000000000000000)
noncomputable def bm12973 : ℝ := (21965087726659695049 / 50000000000000000000)

theorem positive12973 :
    Eplus aL (agent12973.root+dsL) scalar12973.worldRadius world12973.frame
      agent12973.frame tp12973 ≤ -ep12973 := by
  apply positive_check (eT := (14458628084470690773 / 12500000000000000000)) (y := (38044952425940518549 / 100000000000000000000)) (u := (146294206959689963627 / 100000000000000000000))
  · norm_num [world12973, agent12973, scalar12973, tp12973, tm12973, ep12973, em12973, dsL]
  · norm_num [world12973, agent12973, scalar12973, tp12973, tm12973, ep12973, em12973, dsL]
  · norm_num [world12973, agent12973, scalar12973, tp12973, tm12973, ep12973, em12973, dsL]
  · norm_num [world12973, agent12973, scalar12973, tp12973, tm12973, ep12973, em12973, dsL]
  · norm_num [world12973, agent12973, scalar12973, tp12973, tm12973, ep12973, em12973, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12973, agent12973, tp12973, tm12973, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12973, agent12973, scalar12973, tp12973, tm12973, ep12973, em12973, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12973, agent12973, tp12973, tm12973, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12973, agent12973, scalar12973, tp12973, tm12973, ep12973, em12973, dsL]

theorem negative12973 :
    Eminus aL (agent12973.root+dsL) scalar12973.worldRadius world12973.frame
      agent12973.frame tm12973 ≤ -em12973 := by
  apply negative_check (lo := (13672177892715584811 / 20000000000000000000)) (hi := (8545111182947240507 / 12500000000000000000))
    (y := (-((7164120974072856743 / 10000000000000000000)))) (u := (48850181238331086537 / 100000000000000000000))
  · norm_num [world12973, agent12973, scalar12973, tp12973, tm12973, ep12973, em12973, dsL]
  · norm_num [world12973, agent12973, scalar12973, tp12973, tm12973, ep12973, em12973, dsL]
  · norm_num [world12973, agent12973, scalar12973, tp12973, tm12973, ep12973, em12973, dsL]
  · norm_num [world12973, agent12973, scalar12973, tp12973, tm12973, ep12973, em12973, dsL]
  · norm_num [world12973, agent12973, scalar12973, tp12973, tm12973, ep12973, em12973, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12973, agent12973, tp12973, tm12973, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12973, agent12973, tp12973, tm12973, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12973, agent12973, scalar12973, tp12973, tm12973, ep12973, em12973, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12973, agent12973, tp12973, tm12973, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12973, agent12973, scalar12973, tp12973, tm12973, ep12973, em12973, dsL]

theorem tails12973 :
    exp (-((12973:ℝ)*ep12973)) ≤ scalar12973.upperTail ∧
    exp (-((12973:ℝ)*em12973)) ≤ scalar12973.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12973:ℝ)) (by norm_num [ep12973]) ?_)
      (show bp12973^8 ≤ scalar12973.upperTail by norm_num [bp12973, scalar12973])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12973, bp12973, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12973:ℝ)) (by norm_num [em12973]) ?_)
      (show bm12973^8 ≤ scalar12973.lowerTail by norm_num [bm12973, scalar12973])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12973, bm12973, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12973 :
    agent12973.root+dsL+scalar12973.worldRadius < √(1/100/aL) ∧
    2*(agent12973.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12973, agent12973, scalar12973, tp12973, tm12973, ep12973, em12973, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12973, agent12973, scalar12973, tp12973, tm12973, ep12973, em12973, dsL]

noncomputable def master12973 : MasterCertificate 12973 world12973 agent12973 :=
  master scalar12973 dsL tp12973 tm12973 ep12973 em12973
    (by norm_num [dsL]) (by norm_num [tp12973]) (by norm_num [tm12973])
    (by norm_num [ep12973]) (by norm_num [em12973])
    positive12973 negative12973 tails12973.1 tails12973.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12973.1 tailGuards12973.2

theorem preserves12973 : master12973.toScalarCertificate = scalar12973 := rfl

noncomputable def tp12974 : ℝ := (2340581917 / 10000000000)
noncomputable def tm12974 : ℝ := (-((6116128551 / 10000000000)))
noncomputable def ep12974 : ℝ := (26068361672559227 / 50000000000000000000)
noncomputable def em12974 : ℝ := (2029077080936323 / 4000000000000000000)
noncomputable def bp12974 : ℝ := (42933090766545175519 / 100000000000000000000)
noncomputable def bm12974 : ℝ := (686343645053525839 / 1562500000000000000)

theorem positive12974 :
    Eplus aL (agent12974.root+dsL) scalar12974.worldRadius world12974.frame
      agent12974.frame tp12974 ≤ -ep12974 := by
  apply positive_check (eT := (115669214099025763959 / 100000000000000000000)) (y := (19022824090826020477 / 50000000000000000000)) (u := (14629522481353139609 / 10000000000000000000))
  · norm_num [world12974, agent12974, scalar12974, tp12974, tm12974, ep12974, em12974, dsL]
  · norm_num [world12974, agent12974, scalar12974, tp12974, tm12974, ep12974, em12974, dsL]
  · norm_num [world12974, agent12974, scalar12974, tp12974, tm12974, ep12974, em12974, dsL]
  · norm_num [world12974, agent12974, scalar12974, tp12974, tm12974, ep12974, em12974, dsL]
  · norm_num [world12974, agent12974, scalar12974, tp12974, tm12974, ep12974, em12974, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12974, agent12974, tp12974, tm12974, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12974, agent12974, scalar12974, tp12974, tm12974, ep12974, em12974, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12974, agent12974, tp12974, tm12974, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12974, agent12974, scalar12974, tp12974, tm12974, ep12974, em12974, dsL]

theorem negative12974 :
    Eminus aL (agent12974.root+dsL) scalar12974.worldRadius world12974.frame
      agent12974.frame tm12974 ≤ -em12974 := by
  apply negative_check (lo := (13672150995080188137 / 20000000000000000000)) (hi := (34180377487700470343 / 50000000000000000000))
    (y := (-((71641174023420938899 / 100000000000000000000)))) (u := (3908015894904297 / 8000000000000000))
  · norm_num [world12974, agent12974, scalar12974, tp12974, tm12974, ep12974, em12974, dsL]
  · norm_num [world12974, agent12974, scalar12974, tp12974, tm12974, ep12974, em12974, dsL]
  · norm_num [world12974, agent12974, scalar12974, tp12974, tm12974, ep12974, em12974, dsL]
  · norm_num [world12974, agent12974, scalar12974, tp12974, tm12974, ep12974, em12974, dsL]
  · norm_num [world12974, agent12974, scalar12974, tp12974, tm12974, ep12974, em12974, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12974, agent12974, tp12974, tm12974, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12974, agent12974, tp12974, tm12974, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12974, agent12974, scalar12974, tp12974, tm12974, ep12974, em12974, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12974, agent12974, tp12974, tm12974, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12974, agent12974, scalar12974, tp12974, tm12974, ep12974, em12974, dsL]

theorem tails12974 :
    exp (-((12974:ℝ)*ep12974)) ≤ scalar12974.upperTail ∧
    exp (-((12974:ℝ)*em12974)) ≤ scalar12974.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12974:ℝ)) (by norm_num [ep12974]) ?_)
      (show bp12974^8 ≤ scalar12974.upperTail by norm_num [bp12974, scalar12974])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12974, bp12974, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12974:ℝ)) (by norm_num [em12974]) ?_)
      (show bm12974^8 ≤ scalar12974.lowerTail by norm_num [bm12974, scalar12974])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12974, bm12974, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12974 :
    agent12974.root+dsL+scalar12974.worldRadius < √(1/100/aL) ∧
    2*(agent12974.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12974, agent12974, scalar12974, tp12974, tm12974, ep12974, em12974, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12974, agent12974, scalar12974, tp12974, tm12974, ep12974, em12974, dsL]

noncomputable def master12974 : MasterCertificate 12974 world12974 agent12974 :=
  master scalar12974 dsL tp12974 tm12974 ep12974 em12974
    (by norm_num [dsL]) (by norm_num [tp12974]) (by norm_num [tm12974])
    (by norm_num [ep12974]) (by norm_num [em12974])
    positive12974 negative12974 tails12974.1 tails12974.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12974.1 tailGuards12974.2

theorem preserves12974 : master12974.toScalarCertificate = scalar12974 := rfl

end BstLean.Part268
