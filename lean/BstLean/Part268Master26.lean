import BstLean.Part261Checker
import BstLean.Part268Scalar26
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp13000 : ℝ := (2342774631 / 10000000000)
noncomputable def tm13000 : ℝ := (-((6120986991 / 10000000000)))
noncomputable def ep13000 : ℝ := (52200469958956077 / 100000000000000000000)
noncomputable def em13000 : ℝ := (50782129191863461 / 100000000000000000000)
noncomputable def bp13000 : ℝ := (8563205862790823053 / 20000000000000000000)
noncomputable def bm13000 : ℝ := (43814314831316328129 / 100000000000000000000)

theorem positive13000 :
    Eplus aL (agent13000.root+dsL) scalar13000.worldRadius world13000.frame
      agent13000.frame tp13000 ≤ -ep13000 := by
  apply positive_check (eT := (4627026701726544679 / 4000000000000000000)) (y := (38061428040635024823 / 100000000000000000000)) (u := (1143111811056297329 / 781250000000000000))
  · norm_num [world13000, agent13000, scalar13000, tp13000, tm13000, ep13000, em13000, dsL]
  · norm_num [world13000, agent13000, scalar13000, tp13000, tm13000, ep13000, em13000, dsL]
  · norm_num [world13000, agent13000, scalar13000, tp13000, tm13000, ep13000, em13000, dsL]
  · norm_num [world13000, agent13000, scalar13000, tp13000, tm13000, ep13000, em13000, dsL]
  · norm_num [world13000, agent13000, scalar13000, tp13000, tm13000, ep13000, em13000, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13000, agent13000, tp13000, tm13000, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13000, agent13000, scalar13000, tp13000, tm13000, ep13000, em13000, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13000, agent13000, tp13000, tm13000, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13000, agent13000, scalar13000, tp13000, tm13000, ep13000, em13000, dsL]

theorem negative13000 :
    Eminus aL (agent13000.root+dsL) scalar13000.worldRadius world13000.frame
      agent13000.frame tm13000 ≤ -em13000 := by
  apply negative_check (lo := (4272155718228171499 / 6250000000000000000)) (hi := (13670898298330148797 / 20000000000000000000))
    (y := (-((7163436865019808843 / 10000000000000000000)))) (u := (12213380809441800979 / 25000000000000000000))
  · norm_num [world13000, agent13000, scalar13000, tp13000, tm13000, ep13000, em13000, dsL]
  · norm_num [world13000, agent13000, scalar13000, tp13000, tm13000, ep13000, em13000, dsL]
  · norm_num [world13000, agent13000, scalar13000, tp13000, tm13000, ep13000, em13000, dsL]
  · norm_num [world13000, agent13000, scalar13000, tp13000, tm13000, ep13000, em13000, dsL]
  · norm_num [world13000, agent13000, scalar13000, tp13000, tm13000, ep13000, em13000, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13000, agent13000, tp13000, tm13000, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13000, agent13000, tp13000, tm13000, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13000, agent13000, scalar13000, tp13000, tm13000, ep13000, em13000, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13000, agent13000, tp13000, tm13000, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13000, agent13000, scalar13000, tp13000, tm13000, ep13000, em13000, dsL]

theorem tails13000 :
    exp (-((13000:ℝ)*ep13000)) ≤ scalar13000.upperTail ∧
    exp (-((13000:ℝ)*em13000)) ≤ scalar13000.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13000:ℝ)) (by norm_num [ep13000]) ?_)
      (show bp13000^8 ≤ scalar13000.upperTail by norm_num [bp13000, scalar13000])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13000, bp13000, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13000:ℝ)) (by norm_num [em13000]) ?_)
      (show bm13000^8 ≤ scalar13000.lowerTail by norm_num [bm13000, scalar13000])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13000, bm13000, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13000 :
    agent13000.root+dsL+scalar13000.worldRadius < √(1/100/aL) ∧
    2*(agent13000.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13000, agent13000, scalar13000, tp13000, tm13000, ep13000, em13000, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13000, agent13000, scalar13000, tp13000, tm13000, ep13000, em13000, dsL]

noncomputable def master13000 : MasterCertificate 13000 world13000 agent13000 :=
  master scalar13000 dsL tp13000 tm13000 ep13000 em13000
    (by norm_num [dsL]) (by norm_num [tp13000]) (by norm_num [tm13000])
    (by norm_num [ep13000]) (by norm_num [em13000])
    positive13000 negative13000 tails13000.1 tails13000.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13000.1 tailGuards13000.2

theorem preserves13000 : master13000.toScalarCertificate = scalar13000 := rfl

noncomputable def tp13001 : ℝ := (1171425103 / 5000000000)
noncomputable def tm13001 : ℝ := (-((23910733 / 39062500)))
noncomputable def ep13001 : ℝ := (52202749435880679 / 100000000000000000000)
noncomputable def em13001 : ℝ := (3174004175522161 / 6250000000000000000)
noncomputable def bp13001 : ℝ := (10702912418737960853 / 25000000000000000000)
noncomputable def bm13001 : ℝ := (8762030828651905297 / 20000000000000000000)

theorem positive13001 :
    Eplus aL (agent13001.root+dsL) scalar13001.worldRadius world13001.frame
      agent13001.frame tp13001 ≤ -ep13001 := by
  apply positive_check (eT := (115675853181390574721 / 100000000000000000000)) (y := (7612422789058386347 / 20000000000000000000)) (u := (18289914427845324717 / 12500000000000000000))
  · norm_num [world13001, agent13001, scalar13001, tp13001, tm13001, ep13001, em13001, dsL]
  · norm_num [world13001, agent13001, scalar13001, tp13001, tm13001, ep13001, em13001, dsL]
  · norm_num [world13001, agent13001, scalar13001, tp13001, tm13001, ep13001, em13001, dsL]
  · norm_num [world13001, agent13001, scalar13001, tp13001, tm13001, ep13001, em13001, dsL]
  · norm_num [world13001, agent13001, scalar13001, tp13001, tm13001, ep13001, em13001, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13001, agent13001, tp13001, tm13001, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13001, agent13001, scalar13001, tp13001, tm13001, ep13001, em13001, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13001, agent13001, tp13001, tm13001, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13001, agent13001, scalar13001, tp13001, tm13001, ep13001, em13001, dsL]

theorem negative13001 :
    Eminus aL (agent13001.root+dsL) scalar13001.worldRadius world13001.frame
      agent13001.frame tm13001 ≤ -em13001 := by
  apply negative_check (lo := (68354361230120236151 / 100000000000000000000)) (hi := (8544295153765029519 / 12500000000000000000))
    (y := (-((2865372820173065739 / 4000000000000000000)))) (u := (6106693344840920061 / 12500000000000000000))
  · norm_num [world13001, agent13001, scalar13001, tp13001, tm13001, ep13001, em13001, dsL]
  · norm_num [world13001, agent13001, scalar13001, tp13001, tm13001, ep13001, em13001, dsL]
  · norm_num [world13001, agent13001, scalar13001, tp13001, tm13001, ep13001, em13001, dsL]
  · norm_num [world13001, agent13001, scalar13001, tp13001, tm13001, ep13001, em13001, dsL]
  · norm_num [world13001, agent13001, scalar13001, tp13001, tm13001, ep13001, em13001, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13001, agent13001, tp13001, tm13001, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13001, agent13001, tp13001, tm13001, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13001, agent13001, scalar13001, tp13001, tm13001, ep13001, em13001, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13001, agent13001, tp13001, tm13001, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13001, agent13001, scalar13001, tp13001, tm13001, ep13001, em13001, dsL]

theorem tails13001 :
    exp (-((13001:ℝ)*ep13001)) ≤ scalar13001.upperTail ∧
    exp (-((13001:ℝ)*em13001)) ≤ scalar13001.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13001:ℝ)) (by norm_num [ep13001]) ?_)
      (show bp13001^8 ≤ scalar13001.upperTail by norm_num [bp13001, scalar13001])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13001, bp13001, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13001:ℝ)) (by norm_num [em13001]) ?_)
      (show bm13001^8 ≤ scalar13001.lowerTail by norm_num [bm13001, scalar13001])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13001, bm13001, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13001 :
    agent13001.root+dsL+scalar13001.worldRadius < √(1/100/aL) ∧
    2*(agent13001.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13001, agent13001, scalar13001, tp13001, tm13001, ep13001, em13001, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13001, agent13001, scalar13001, tp13001, tm13001, ep13001, em13001, dsL]

noncomputable def master13001 : MasterCertificate 13001 world13001 agent13001 :=
  master scalar13001 dsL tp13001 tm13001 ep13001 em13001
    (by norm_num [dsL]) (by norm_num [tp13001]) (by norm_num [tm13001])
    (by norm_num [ep13001]) (by norm_num [em13001])
    positive13001 negative13001 tails13001.1 tails13001.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13001.1 tailGuards13001.2

theorem preserves13001 : master13001.toScalarCertificate = scalar13001 := rfl

noncomputable def tp13002 : ℝ := (468585143 / 2000000000)
noncomputable def tm13002 : ℝ := (-((95645439 / 156250000)))
noncomputable def ep13002 : ℝ := (10441005377628789 / 20000000000000000000)
noncomputable def em13002 : ℝ := (50786002556319443 / 100000000000000000000)
noncomputable def bp13002 : ℝ := (21403635824301972153 / 50000000000000000000)
noncomputable def bm13002 : ℝ := (2737874685526342833 / 6250000000000000000)

theorem positive13002 :
    Eplus aL (agent13002.root+dsL) scalar13002.worldRadius world13002.frame
      agent13002.frame tp13002 ≤ -ep13002 := by
  apply positive_check (eT := (115676038378085161511 / 100000000000000000000)) (y := (3806279906987357371 / 10000000000000000000)) (u := (146320317895794340001 / 100000000000000000000))
  · norm_num [world13002, agent13002, scalar13002, tp13002, tm13002, ep13002, em13002, dsL]
  · norm_num [world13002, agent13002, scalar13002, tp13002, tm13002, ep13002, em13002, dsL]
  · norm_num [world13002, agent13002, scalar13002, tp13002, tm13002, ep13002, em13002, dsL]
  · norm_num [world13002, agent13002, scalar13002, tp13002, tm13002, ep13002, em13002, dsL]
  · norm_num [world13002, agent13002, scalar13002, tp13002, tm13002, ep13002, em13002, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13002, agent13002, tp13002, tm13002, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13002, agent13002, scalar13002, tp13002, tm13002, ep13002, em13002, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13002, agent13002, tp13002, tm13002, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13002, agent13002, scalar13002, tp13002, tm13002, ep13002, em13002, dsL]

theorem negative13002 :
    Eminus aL (agent13002.root+dsL) scalar13002.worldRadius world13002.frame
      agent13002.frame tm13002 ≤ -em13002 := by
  apply negative_check (lo := (34177115899830726387 / 50000000000000000000)) (hi := (2734169271986458111 / 4000000000000000000))
    (y := (-((4477141910613701931 / 6250000000000000000)))) (u := (2442678557675568937 / 5000000000000000000))
  · norm_num [world13002, agent13002, scalar13002, tp13002, tm13002, ep13002, em13002, dsL]
  · norm_num [world13002, agent13002, scalar13002, tp13002, tm13002, ep13002, em13002, dsL]
  · norm_num [world13002, agent13002, scalar13002, tp13002, tm13002, ep13002, em13002, dsL]
  · norm_num [world13002, agent13002, scalar13002, tp13002, tm13002, ep13002, em13002, dsL]
  · norm_num [world13002, agent13002, scalar13002, tp13002, tm13002, ep13002, em13002, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13002, agent13002, tp13002, tm13002, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13002, agent13002, tp13002, tm13002, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13002, agent13002, scalar13002, tp13002, tm13002, ep13002, em13002, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13002, agent13002, tp13002, tm13002, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13002, agent13002, scalar13002, tp13002, tm13002, ep13002, em13002, dsL]

theorem tails13002 :
    exp (-((13002:ℝ)*ep13002)) ≤ scalar13002.upperTail ∧
    exp (-((13002:ℝ)*em13002)) ≤ scalar13002.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13002:ℝ)) (by norm_num [ep13002]) ?_)
      (show bp13002^8 ≤ scalar13002.upperTail by norm_num [bp13002, scalar13002])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13002, bp13002, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13002:ℝ)) (by norm_num [em13002]) ?_)
      (show bm13002^8 ≤ scalar13002.lowerTail by norm_num [bm13002, scalar13002])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13002, bm13002, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13002 :
    agent13002.root+dsL+scalar13002.worldRadius < √(1/100/aL) ∧
    2*(agent13002.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13002, agent13002, scalar13002, tp13002, tm13002, ep13002, em13002, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13002, agent13002, scalar13002, tp13002, tm13002, ep13002, em13002, dsL]

noncomputable def master13002 : MasterCertificate 13002 world13002 agent13002 :=
  master scalar13002 dsL tp13002 tm13002 ep13002 em13002
    (by norm_num [dsL]) (by norm_num [tp13002]) (by norm_num [tm13002])
    (by norm_num [ep13002]) (by norm_num [em13002])
    positive13002 negative13002 tails13002.1 tails13002.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13002.1 tailGuards13002.2

theorem preserves13002 : master13002.toScalarCertificate = scalar13002 := rfl

noncomputable def tp13003 : ℝ := (2343001193 / 10000000000)
noncomputable def tm13003 : ℝ := (-((6121468373 / 10000000000)))
noncomputable def ep13003 : ℝ := (10441460749391217 / 20000000000000000000)
noncomputable def em13003 : ℝ := (12696984440431867 / 25000000000000000000)
noncomputable def bp13003 : ℝ := (42802894239128520031 / 100000000000000000000)
noncomputable def bm13003 : ℝ := (5475229545342131493 / 12500000000000000000)

theorem positive13003 :
    Eplus aL (agent13003.root+dsL) scalar13003.worldRadius world13003.frame
      agent13003.frame tp13003 ≤ -ep13003 := by
  apply positive_check (eT := (57838111692472737063 / 50000000000000000000)) (y := (38063483877481153271 / 100000000000000000000)) (u := (73160659955946831161 / 50000000000000000000))
  · norm_num [world13003, agent13003, scalar13003, tp13003, tm13003, ep13003, em13003, dsL]
  · norm_num [world13003, agent13003, scalar13003, tp13003, tm13003, ep13003, em13003, dsL]
  · norm_num [world13003, agent13003, scalar13003, tp13003, tm13003, ep13003, em13003, dsL]
  · norm_num [world13003, agent13003, scalar13003, tp13003, tm13003, ep13003, em13003, dsL]
  · norm_num [world13003, agent13003, scalar13003, tp13003, tm13003, ep13003, em13003, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13003, agent13003, tp13003, tm13003, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13003, agent13003, scalar13003, tp13003, tm13003, ep13003, em13003, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13003, agent13003, tp13003, tm13003, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13003, agent13003, scalar13003, tp13003, tm13003, ep13003, em13003, dsL]

theorem negative13003 :
    Eminus aL (agent13003.root+dsL) scalar13003.worldRadius world13003.frame
      agent13003.frame tm13003 ≤ -em13003 := by
  apply negative_check (lo := (68354103038724403713 / 100000000000000000000)) (hi := (34177051519362201857 / 50000000000000000000))
    (y := (-((7163421959558199899 / 10000000000000000000)))) (u := (48853596056252981779 / 100000000000000000000))
  · norm_num [world13003, agent13003, scalar13003, tp13003, tm13003, ep13003, em13003, dsL]
  · norm_num [world13003, agent13003, scalar13003, tp13003, tm13003, ep13003, em13003, dsL]
  · norm_num [world13003, agent13003, scalar13003, tp13003, tm13003, ep13003, em13003, dsL]
  · norm_num [world13003, agent13003, scalar13003, tp13003, tm13003, ep13003, em13003, dsL]
  · norm_num [world13003, agent13003, scalar13003, tp13003, tm13003, ep13003, em13003, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13003, agent13003, tp13003, tm13003, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13003, agent13003, tp13003, tm13003, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13003, agent13003, scalar13003, tp13003, tm13003, ep13003, em13003, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13003, agent13003, tp13003, tm13003, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13003, agent13003, scalar13003, tp13003, tm13003, ep13003, em13003, dsL]

theorem tails13003 :
    exp (-((13003:ℝ)*ep13003)) ≤ scalar13003.upperTail ∧
    exp (-((13003:ℝ)*em13003)) ≤ scalar13003.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13003:ℝ)) (by norm_num [ep13003]) ?_)
      (show bp13003^8 ≤ scalar13003.upperTail by norm_num [bp13003, scalar13003])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13003, bp13003, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13003:ℝ)) (by norm_num [em13003]) ?_)
      (show bm13003^8 ≤ scalar13003.lowerTail by norm_num [bm13003, scalar13003])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13003, bm13003, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13003 :
    agent13003.root+dsL+scalar13003.worldRadius < √(1/100/aL) ∧
    2*(agent13003.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13003, agent13003, scalar13003, tp13003, tm13003, ep13003, em13003, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13003, agent13003, scalar13003, tp13003, tm13003, ep13003, em13003, dsL]

noncomputable def master13003 : MasterCertificate 13003 world13003 agent13003 :=
  master scalar13003 dsL tp13003 tm13003 ep13003 em13003
    (by norm_num [dsL]) (by norm_num [tp13003]) (by norm_num [tm13003])
    (by norm_num [ep13003]) (by norm_num [em13003])
    positive13003 negative13003 tails13003.1 tails13003.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13003.1 tailGuards13003.2

theorem preserves13003 : master13003.toScalarCertificate = scalar13003 := rfl

noncomputable def tp13004 : ℝ := (1171538333 / 5000000000)
noncomputable def tm13004 : ℝ := (-((3060814337 / 5000000000)))
noncomputable def ep13004 : ℝ := (13052394610503087 / 25000000000000000000)
noncomputable def em13004 : ℝ := (1269746773814931 / 2500000000000000000)
noncomputable def bp13004 : ℝ := (171194074155873231 / 400000000000000000)
noncomputable def bm13004 : ℝ := (2189883968707890301 / 5000000000000000000)

theorem positive13004 :
    Eplus aL (agent13004.root+dsL) scalar13004.worldRadius world13004.frame
      agent13004.frame tp13004 ≤ -ep13004 := by
  apply positive_check (eT := (115676408388863022527 / 100000000000000000000)) (y := (38064169121956472149 / 100000000000000000000)) (u := (36580580643522477991 / 25000000000000000000))
  · norm_num [world13004, agent13004, scalar13004, tp13004, tm13004, ep13004, em13004, dsL]
  · norm_num [world13004, agent13004, scalar13004, tp13004, tm13004, ep13004, em13004, dsL]
  · norm_num [world13004, agent13004, scalar13004, tp13004, tm13004, ep13004, em13004, dsL]
  · norm_num [world13004, agent13004, scalar13004, tp13004, tm13004, ep13004, em13004, dsL]
  · norm_num [world13004, agent13004, scalar13004, tp13004, tm13004, ep13004, em13004, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13004, agent13004, tp13004, tm13004, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13004, agent13004, scalar13004, tp13004, tm13004, ep13004, em13004, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13004, agent13004, tp13004, tm13004, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13004, agent13004, scalar13004, tp13004, tm13004, ep13004, em13004, dsL]

theorem negative13004 :
    Eminus aL (agent13004.root+dsL) scalar13004.worldRadius world13004.frame
      agent13004.frame tm13004 ≤ -em13004 := by
  apply negative_check (lo := (68353974118912531923 / 100000000000000000000)) (hi := (17088493529728132981 / 25000000000000000000))
    (y := (-((71634169359687103947 / 100000000000000000000)))) (u := (9770724119660062701 / 20000000000000000000))
  · norm_num [world13004, agent13004, scalar13004, tp13004, tm13004, ep13004, em13004, dsL]
  · norm_num [world13004, agent13004, scalar13004, tp13004, tm13004, ep13004, em13004, dsL]
  · norm_num [world13004, agent13004, scalar13004, tp13004, tm13004, ep13004, em13004, dsL]
  · norm_num [world13004, agent13004, scalar13004, tp13004, tm13004, ep13004, em13004, dsL]
  · norm_num [world13004, agent13004, scalar13004, tp13004, tm13004, ep13004, em13004, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13004, agent13004, tp13004, tm13004, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13004, agent13004, tp13004, tm13004, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13004, agent13004, scalar13004, tp13004, tm13004, ep13004, em13004, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13004, agent13004, tp13004, tm13004, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13004, agent13004, scalar13004, tp13004, tm13004, ep13004, em13004, dsL]

theorem tails13004 :
    exp (-((13004:ℝ)*ep13004)) ≤ scalar13004.upperTail ∧
    exp (-((13004:ℝ)*em13004)) ≤ scalar13004.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13004:ℝ)) (by norm_num [ep13004]) ?_)
      (show bp13004^8 ≤ scalar13004.upperTail by norm_num [bp13004, scalar13004])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13004, bp13004, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13004:ℝ)) (by norm_num [em13004]) ?_)
      (show bm13004^8 ≤ scalar13004.lowerTail by norm_num [bm13004, scalar13004])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13004, bm13004, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13004 :
    agent13004.root+dsL+scalar13004.worldRadius < √(1/100/aL) ∧
    2*(agent13004.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13004, agent13004, scalar13004, tp13004, tm13004, ep13004, em13004, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13004, agent13004, scalar13004, tp13004, tm13004, ep13004, em13004, dsL]

noncomputable def master13004 : MasterCertificate 13004 world13004 agent13004 :=
  master scalar13004 dsL tp13004 tm13004 ep13004 em13004
    (by norm_num [dsL]) (by norm_num [tp13004]) (by norm_num [tm13004])
    (by norm_num [ep13004]) (by norm_num [em13004])
    positive13004 negative13004 tails13004.1 tails13004.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13004.1 tailGuards13004.2

theorem preserves13004 : master13004.toScalarCertificate = scalar13004 := rfl

noncomputable def tp13005 : ℝ := (2343152059 / 10000000000)
noncomputable def tm13005 : ℝ := (-((6121789097 / 10000000000)))
noncomputable def ep13005 : ℝ := (52211853354220449 / 100000000000000000000)
noncomputable def em13005 : ℝ := (50791804335114717 / 100000000000000000000)
noncomputable def bp13005 : ℝ := (334329241341455329 / 781250000000000000)
noncomputable def bm13005 : ℝ := (43793522432004584407 / 100000000000000000000)

theorem positive13005 :
    Eplus aL (agent13005.root+dsL) scalar13005.worldRadius world13005.frame
      agent13005.frame tp13005 ≤ -ep13005 := by
  apply positive_check (eT := (115676592850643438117 / 100000000000000000000)) (y := (38064853247487899929 / 100000000000000000000)) (u := (146323323605880972553 / 100000000000000000000))
  · norm_num [world13005, agent13005, scalar13005, tp13005, tm13005, ep13005, em13005, dsL]
  · norm_num [world13005, agent13005, scalar13005, tp13005, tm13005, ep13005, em13005, dsL]
  · norm_num [world13005, agent13005, scalar13005, tp13005, tm13005, ep13005, em13005, dsL]
  · norm_num [world13005, agent13005, scalar13005, tp13005, tm13005, ep13005, em13005, dsL]
  · norm_num [world13005, agent13005, scalar13005, tp13005, tm13005, ep13005, em13005, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13005, agent13005, tp13005, tm13005, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13005, agent13005, scalar13005, tp13005, tm13005, ep13005, em13005, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13005, agent13005, tp13005, tm13005, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13005, agent13005, scalar13005, tp13005, tm13005, ep13005, em13005, dsL]

theorem negative13005 :
    Eminus aL (agent13005.root+dsL) scalar13005.worldRadius world13005.frame
      agent13005.frame tm13005 ≤ -em13005 := by
  apply negative_check (lo := (68353844623900223583 / 100000000000000000000)) (hi := (2136057644496881987 / 3125000000000000000))
    (y := (-((223856629510712203 / 312500000000000000)))) (u := (9770728801426679159 / 20000000000000000000))
  · norm_num [world13005, agent13005, scalar13005, tp13005, tm13005, ep13005, em13005, dsL]
  · norm_num [world13005, agent13005, scalar13005, tp13005, tm13005, ep13005, em13005, dsL]
  · norm_num [world13005, agent13005, scalar13005, tp13005, tm13005, ep13005, em13005, dsL]
  · norm_num [world13005, agent13005, scalar13005, tp13005, tm13005, ep13005, em13005, dsL]
  · norm_num [world13005, agent13005, scalar13005, tp13005, tm13005, ep13005, em13005, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13005, agent13005, tp13005, tm13005, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13005, agent13005, tp13005, tm13005, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13005, agent13005, scalar13005, tp13005, tm13005, ep13005, em13005, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13005, agent13005, tp13005, tm13005, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13005, agent13005, scalar13005, tp13005, tm13005, ep13005, em13005, dsL]

theorem tails13005 :
    exp (-((13005:ℝ)*ep13005)) ≤ scalar13005.upperTail ∧
    exp (-((13005:ℝ)*em13005)) ≤ scalar13005.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13005:ℝ)) (by norm_num [ep13005]) ?_)
      (show bp13005^8 ≤ scalar13005.upperTail by norm_num [bp13005, scalar13005])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13005, bp13005, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13005:ℝ)) (by norm_num [em13005]) ?_)
      (show bm13005^8 ≤ scalar13005.lowerTail by norm_num [bm13005, scalar13005])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13005, bm13005, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13005 :
    agent13005.root+dsL+scalar13005.worldRadius < √(1/100/aL) ∧
    2*(agent13005.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13005, agent13005, scalar13005, tp13005, tm13005, ep13005, em13005, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13005, agent13005, scalar13005, tp13005, tm13005, ep13005, em13005, dsL]

noncomputable def master13005 : MasterCertificate 13005 world13005 agent13005 :=
  master scalar13005 dsL tp13005 tm13005 ep13005 em13005
    (by norm_num [dsL]) (by norm_num [tp13005]) (by norm_num [tm13005])
    (by norm_num [ep13005]) (by norm_num [em13005])
    positive13005 negative13005 tails13005.1 tails13005.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13005.1 tailGuards13005.2

theorem preserves13005 : master13005.toScalarCertificate = scalar13005 := rfl

noncomputable def tp13006 : ℝ := (585806869 / 2500000000)
noncomputable def tm13006 : ℝ := (-((3060974619 / 5000000000)))
noncomputable def ep13006 : ℝ := (52214126251137251 / 100000000000000000000)
noncomputable def em13006 : ℝ := (25396867928594627 / 50000000000000000000)
noncomputable def bp13006 : ℝ := (10697442212598076087 / 25000000000000000000)
noncomputable def bm13006 : ℝ := (10947341749300614191 / 25000000000000000000)

theorem positive13006 :
    Eplus aL (agent13006.root+dsL) scalar13006.worldRadius world13006.frame
      agent13006.frame tp13006 ≤ -ep13006 := by
  apply positive_check (eT := (23135355503600987379 / 20000000000000000000)) (y := (761310763273891279 / 2000000000000000000)) (u := (146324325801470574763 / 100000000000000000000))
  · norm_num [world13006, agent13006, scalar13006, tp13006, tm13006, ep13006, em13006, dsL]
  · norm_num [world13006, agent13006, scalar13006, tp13006, tm13006, ep13006, em13006, dsL]
  · norm_num [world13006, agent13006, scalar13006, tp13006, tm13006, ep13006, em13006, dsL]
  · norm_num [world13006, agent13006, scalar13006, tp13006, tm13006, ep13006, em13006, dsL]
  · norm_num [world13006, agent13006, scalar13006, tp13006, tm13006, ep13006, em13006, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13006, agent13006, tp13006, tm13006, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13006, agent13006, scalar13006, tp13006, tm13006, ep13006, em13006, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13006, agent13006, tp13006, tm13006, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13006, agent13006, scalar13006, tp13006, tm13006, ep13006, em13006, dsL]

theorem negative13006 :
    Eminus aL (agent13006.root+dsL) scalar13006.worldRadius world13006.frame
      agent13006.frame tm13006 ≤ -em13006 := by
  apply negative_check (lo := (4272107266872563611 / 6250000000000000000)) (hi := (68353716269961017777 / 100000000000000000000))
    (y := (-((71634071035904037157 / 100000000000000000000)))) (u := (48853668633051865639 / 100000000000000000000))
  · norm_num [world13006, agent13006, scalar13006, tp13006, tm13006, ep13006, em13006, dsL]
  · norm_num [world13006, agent13006, scalar13006, tp13006, tm13006, ep13006, em13006, dsL]
  · norm_num [world13006, agent13006, scalar13006, tp13006, tm13006, ep13006, em13006, dsL]
  · norm_num [world13006, agent13006, scalar13006, tp13006, tm13006, ep13006, em13006, dsL]
  · norm_num [world13006, agent13006, scalar13006, tp13006, tm13006, ep13006, em13006, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13006, agent13006, tp13006, tm13006, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13006, agent13006, tp13006, tm13006, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13006, agent13006, scalar13006, tp13006, tm13006, ep13006, em13006, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13006, agent13006, tp13006, tm13006, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13006, agent13006, scalar13006, tp13006, tm13006, ep13006, em13006, dsL]

theorem tails13006 :
    exp (-((13006:ℝ)*ep13006)) ≤ scalar13006.upperTail ∧
    exp (-((13006:ℝ)*em13006)) ≤ scalar13006.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13006:ℝ)) (by norm_num [ep13006]) ?_)
      (show bp13006^8 ≤ scalar13006.upperTail by norm_num [bp13006, scalar13006])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13006, bp13006, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13006:ℝ)) (by norm_num [em13006]) ?_)
      (show bm13006^8 ≤ scalar13006.lowerTail by norm_num [bm13006, scalar13006])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13006, bm13006, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13006 :
    agent13006.root+dsL+scalar13006.worldRadius < √(1/100/aL) ∧
    2*(agent13006.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13006, agent13006, scalar13006, tp13006, tm13006, ep13006, em13006, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13006, agent13006, scalar13006, tp13006, tm13006, ep13006, em13006, dsL]

noncomputable def master13006 : MasterCertificate 13006 world13006 agent13006 :=
  master scalar13006 dsL tp13006 tm13006 ep13006 em13006
    (by norm_num [dsL]) (by norm_num [tp13006]) (by norm_num [tm13006])
    (by norm_num [ep13006]) (by norm_num [em13006])
    positive13006 negative13006 tails13006.1 tails13006.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13006.1 tailGuards13006.2

theorem preserves13006 : master13006.toScalarCertificate = scalar13006 := rfl

noncomputable def tp13007 : ℝ := (117165139 / 500000000)
noncomputable def tm13007 : ℝ := (-((1224421847 / 2000000000)))
noncomputable def ep13007 : ℝ := (6527049819348073 / 12500000000000000000)
noncomputable def em13007 : ℝ := (12698916709249079 / 25000000000000000000)
noncomputable def bp13007 : ℝ := (42785395425737639409 / 100000000000000000000)
noncomputable def bm13007 : ℝ := (43785212131303022013 / 100000000000000000000)

theorem positive13007 :
    Eplus aL (agent13007.root+dsL) scalar13007.worldRadius world13007.frame
      agent13007.frame tp13007 ≤ -ep13007 := by
  apply positive_check (eT := (28919240351503020489 / 25000000000000000000)) (y := (19033110665526782059 / 50000000000000000000)) (u := (2926506508898346849 / 2000000000000000000))
  · norm_num [world13007, agent13007, scalar13007, tp13007, tm13007, ep13007, em13007, dsL]
  · norm_num [world13007, agent13007, scalar13007, tp13007, tm13007, ep13007, em13007, dsL]
  · norm_num [world13007, agent13007, scalar13007, tp13007, tm13007, ep13007, em13007, dsL]
  · norm_num [world13007, agent13007, scalar13007, tp13007, tm13007, ep13007, em13007, dsL]
  · norm_num [world13007, agent13007, scalar13007, tp13007, tm13007, ep13007, em13007, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13007, agent13007, tp13007, tm13007, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13007, agent13007, scalar13007, tp13007, tm13007, ep13007, em13007, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13007, agent13007, tp13007, tm13007, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13007, agent13007, scalar13007, tp13007, tm13007, ep13007, em13007, dsL]

theorem negative13007 :
    Eminus aL (agent13007.root+dsL) scalar13007.worldRadius world13007.frame
      agent13007.frame tm13007 ≤ -em13007 := by
  apply negative_check (lo := (68353588470819056493 / 100000000000000000000)) (hi := (34176794235409528247 / 50000000000000000000))
    (y := (-((17908504961886266647 / 25000000000000000000)))) (u := (190834740783006001 / 390625000000000000))
  · norm_num [world13007, agent13007, scalar13007, tp13007, tm13007, ep13007, em13007, dsL]
  · norm_num [world13007, agent13007, scalar13007, tp13007, tm13007, ep13007, em13007, dsL]
  · norm_num [world13007, agent13007, scalar13007, tp13007, tm13007, ep13007, em13007, dsL]
  · norm_num [world13007, agent13007, scalar13007, tp13007, tm13007, ep13007, em13007, dsL]
  · norm_num [world13007, agent13007, scalar13007, tp13007, tm13007, ep13007, em13007, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13007, agent13007, tp13007, tm13007, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13007, agent13007, tp13007, tm13007, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13007, agent13007, scalar13007, tp13007, tm13007, ep13007, em13007, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13007, agent13007, tp13007, tm13007, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13007, agent13007, scalar13007, tp13007, tm13007, ep13007, em13007, dsL]

theorem tails13007 :
    exp (-((13007:ℝ)*ep13007)) ≤ scalar13007.upperTail ∧
    exp (-((13007:ℝ)*em13007)) ≤ scalar13007.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13007:ℝ)) (by norm_num [ep13007]) ?_)
      (show bp13007^8 ≤ scalar13007.upperTail by norm_num [bp13007, scalar13007])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13007, bp13007, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13007:ℝ)) (by norm_num [em13007]) ?_)
      (show bm13007^8 ≤ scalar13007.lowerTail by norm_num [bm13007, scalar13007])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13007, bm13007, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13007 :
    agent13007.root+dsL+scalar13007.worldRadius < √(1/100/aL) ∧
    2*(agent13007.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13007, agent13007, scalar13007, tp13007, tm13007, ep13007, em13007, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13007, agent13007, scalar13007, tp13007, tm13007, ep13007, em13007, dsL]

noncomputable def master13007 : MasterCertificate 13007 world13007 agent13007 :=
  master scalar13007 dsL tp13007 tm13007 ep13007 em13007
    (by norm_num [dsL]) (by norm_num [tp13007]) (by norm_num [tm13007])
    (by norm_num [ep13007]) (by norm_num [em13007])
    positive13007 negative13007 tails13007.1 tails13007.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13007.1 tailGuards13007.2

theorem preserves13007 : master13007.toScalarCertificate = scalar13007 := rfl

noncomputable def tp13008 : ℝ := (2343378089 / 10000000000)
noncomputable def tm13008 : ℝ := (-((306113461 / 500000000)))
noncomputable def ep13008 : ℝ := (3263666793119801 / 6250000000000000000)
noncomputable def em13008 : ℝ := (50797595798321043 / 100000000000000000000)
noncomputable def bp13008 : ℝ := (42781023713511249879 / 100000000000000000000)
noncomputable def bm13008 : ℝ := (43781058885196041737 / 100000000000000000000)

theorem positive13008 :
    Eplus aL (agent13008.root+dsL) scalar13008.worldRadius world13008.frame
      agent13008.frame tp13008 ≤ -ep13008 := by
  apply positive_check (eT := (115677145363012815099 / 100000000000000000000)) (y := (38066905109371476449 / 100000000000000000000)) (u := (7316316299459354897 / 5000000000000000000))
  · norm_num [world13008, agent13008, scalar13008, tp13008, tm13008, ep13008, em13008, dsL]
  · norm_num [world13008, agent13008, scalar13008, tp13008, tm13008, ep13008, em13008, dsL]
  · norm_num [world13008, agent13008, scalar13008, tp13008, tm13008, ep13008, em13008, dsL]
  · norm_num [world13008, agent13008, scalar13008, tp13008, tm13008, ep13008, em13008, dsL]
  · norm_num [world13008, agent13008, scalar13008, tp13008, tm13008, ep13008, em13008, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13008, agent13008, tp13008, tm13008, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13008, agent13008, scalar13008, tp13008, tm13008, ep13008, em13008, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13008, agent13008, tp13008, tm13008, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13008, agent13008, scalar13008, tp13008, tm13008, ep13008, em13008, dsL]

theorem negative13008 :
    Eminus aL (agent13008.root+dsL) scalar13008.worldRadius world13008.frame
      agent13008.frame tm13008 ≤ -em13008 := by
  apply negative_check (lo := (68353460665698423817 / 100000000000000000000)) (hi := (34176730332849211909 / 50000000000000000000))
    (y := (-((17908492262564694713 / 25000000000000000000)))) (u := (24426859228403229973 / 50000000000000000000))
  · norm_num [world13008, agent13008, scalar13008, tp13008, tm13008, ep13008, em13008, dsL]
  · norm_num [world13008, agent13008, scalar13008, tp13008, tm13008, ep13008, em13008, dsL]
  · norm_num [world13008, agent13008, scalar13008, tp13008, tm13008, ep13008, em13008, dsL]
  · norm_num [world13008, agent13008, scalar13008, tp13008, tm13008, ep13008, em13008, dsL]
  · norm_num [world13008, agent13008, scalar13008, tp13008, tm13008, ep13008, em13008, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13008, agent13008, tp13008, tm13008, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13008, agent13008, tp13008, tm13008, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13008, agent13008, scalar13008, tp13008, tm13008, ep13008, em13008, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13008, agent13008, tp13008, tm13008, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13008, agent13008, scalar13008, tp13008, tm13008, ep13008, em13008, dsL]

theorem tails13008 :
    exp (-((13008:ℝ)*ep13008)) ≤ scalar13008.upperTail ∧
    exp (-((13008:ℝ)*em13008)) ≤ scalar13008.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13008:ℝ)) (by norm_num [ep13008]) ?_)
      (show bp13008^8 ≤ scalar13008.upperTail by norm_num [bp13008, scalar13008])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13008, bp13008, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13008:ℝ)) (by norm_num [em13008]) ?_)
      (show bm13008^8 ≤ scalar13008.lowerTail by norm_num [bm13008, scalar13008])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13008, bm13008, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13008 :
    agent13008.root+dsL+scalar13008.worldRadius < √(1/100/aL) ∧
    2*(agent13008.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13008, agent13008, scalar13008, tp13008, tm13008, ep13008, em13008, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13008, agent13008, scalar13008, tp13008, tm13008, ep13008, em13008, dsL]

noncomputable def master13008 : MasterCertificate 13008 world13008 agent13008 :=
  master scalar13008 dsL tp13008 tm13008 ep13008 em13008
    (by norm_num [dsL]) (by norm_num [tp13008]) (by norm_num [tm13008])
    (by norm_num [ep13008]) (by norm_num [em13008])
    positive13008 negative13008 tails13008.1 tails13008.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13008.1 tailGuards13008.2

theorem preserves13008 : master13008.toScalarCertificate = scalar13008 := rfl

noncomputable def tp13009 : ℝ := (468690677 / 2000000000)
noncomputable def tm13009 : ℝ := (-((6122429213 / 10000000000)))
noncomputable def ep13009 : ℝ := (3263808699732869 / 6250000000000000000)
noncomputable def em13009 : ℝ := (25399762554900061 / 50000000000000000000)
noncomputable def bp13009 : ℝ := (21388325973680398639 / 50000000000000000000)
noncomputable def bm13009 : ℝ := (43776905572671905969 / 100000000000000000000)

theorem positive13009 :
    Eplus aL (agent13009.root+dsL) scalar13009.worldRadius world13009.frame
      agent13009.frame tp13009 ≤ -ep13009 := by
  apply positive_check (eT := (57838664629779002677 / 50000000000000000000)) (y := (19033794392836777331 / 50000000000000000000)) (u := (73163663195510669481 / 50000000000000000000))
  · norm_num [world13009, agent13009, scalar13009, tp13009, tm13009, ep13009, em13009, dsL]
  · norm_num [world13009, agent13009, scalar13009, tp13009, tm13009, ep13009, em13009, dsL]
  · norm_num [world13009, agent13009, scalar13009, tp13009, tm13009, ep13009, em13009, dsL]
  · norm_num [world13009, agent13009, scalar13009, tp13009, tm13009, ep13009, em13009, dsL]
  · norm_num [world13009, agent13009, scalar13009, tp13009, tm13009, ep13009, em13009, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13009, agent13009, tp13009, tm13009, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13009, agent13009, scalar13009, tp13009, tm13009, ep13009, em13009, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13009, agent13009, tp13009, tm13009, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13009, agent13009, scalar13009, tp13009, tm13009, ep13009, em13009, dsL]

theorem negative13009 :
    Eminus aL (agent13009.root+dsL) scalar13009.worldRadius world13009.frame
      agent13009.frame tm13009 ≤ -em13009 := by
  apply negative_check (lo := (273413331078864679 / 400000000000000000)) (hi := (68353332769716169751 / 100000000000000000000))
    (y := (-((35816959594505961149 / 50000000000000000000)))) (u := (4885374281588569117 / 10000000000000000000))
  · norm_num [world13009, agent13009, scalar13009, tp13009, tm13009, ep13009, em13009, dsL]
  · norm_num [world13009, agent13009, scalar13009, tp13009, tm13009, ep13009, em13009, dsL]
  · norm_num [world13009, agent13009, scalar13009, tp13009, tm13009, ep13009, em13009, dsL]
  · norm_num [world13009, agent13009, scalar13009, tp13009, tm13009, ep13009, em13009, dsL]
  · norm_num [world13009, agent13009, scalar13009, tp13009, tm13009, ep13009, em13009, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13009, agent13009, tp13009, tm13009, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13009, agent13009, tp13009, tm13009, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13009, agent13009, scalar13009, tp13009, tm13009, ep13009, em13009, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13009, agent13009, tp13009, tm13009, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13009, agent13009, scalar13009, tp13009, tm13009, ep13009, em13009, dsL]

theorem tails13009 :
    exp (-((13009:ℝ)*ep13009)) ≤ scalar13009.upperTail ∧
    exp (-((13009:ℝ)*em13009)) ≤ scalar13009.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13009:ℝ)) (by norm_num [ep13009]) ?_)
      (show bp13009^8 ≤ scalar13009.upperTail by norm_num [bp13009, scalar13009])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13009, bp13009, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13009:ℝ)) (by norm_num [em13009]) ?_)
      (show bm13009^8 ≤ scalar13009.lowerTail by norm_num [bm13009, scalar13009])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13009, bm13009, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13009 :
    agent13009.root+dsL+scalar13009.worldRadius < √(1/100/aL) ∧
    2*(agent13009.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13009, agent13009, scalar13009, tp13009, tm13009, ep13009, em13009, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13009, agent13009, scalar13009, tp13009, tm13009, ep13009, em13009, dsL]

noncomputable def master13009 : MasterCertificate 13009 world13009 agent13009 :=
  master scalar13009 dsL tp13009 tm13009 ep13009 em13009
    (by norm_num [dsL]) (by norm_num [tp13009]) (by norm_num [tm13009])
    (by norm_num [ep13009]) (by norm_num [em13009])
    positive13009 negative13009 tails13009.1 tails13009.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13009.1 tailGuards13009.2

theorem preserves13009 : master13009.toScalarCertificate = scalar13009 := rfl

noncomputable def tp13010 : ℝ := (2343600349 / 10000000000)
noncomputable def tm13010 : ℝ := (-((306140309 / 500000000)))
noncomputable def ep13010 : ℝ := (13056140991251199 / 25000000000000000000)
noncomputable def em13010 : ℝ := (6350366634453351 / 12500000000000000000)
noncomputable def bp13010 : ℝ := (8554267678251861433 / 20000000000000000000)
noncomputable def bm13010 : ℝ := (21885849934548777791 / 50000000000000000000)

theorem positive13010 :
    Eplus aL (agent13010.root+dsL) scalar13010.worldRadius world13010.frame
      agent13010.frame tp13010 ≤ -ep13010 := by
  apply positive_check (eT := (115678028386833127373 / 100000000000000000000)) (y := (2379222296132022369 / 6250000000000000000)) (u := (29265455899337876093 / 20000000000000000000))
  · norm_num [world13010, agent13010, scalar13010, tp13010, tm13010, ep13010, em13010, dsL]
  · norm_num [world13010, agent13010, scalar13010, tp13010, tm13010, ep13010, em13010, dsL]
  · norm_num [world13010, agent13010, scalar13010, tp13010, tm13010, ep13010, em13010, dsL]
  · norm_num [world13010, agent13010, scalar13010, tp13010, tm13010, ep13010, em13010, dsL]
  · norm_num [world13010, agent13010, scalar13010, tp13010, tm13010, ep13010, em13010, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13010, agent13010, tp13010, tm13010, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13010, agent13010, scalar13010, tp13010, tm13010, ep13010, em13010, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13010, agent13010, tp13010, tm13010, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13010, agent13010, scalar13010, tp13010, tm13010, ep13010, em13010, dsL]

theorem negative13010 :
    Eminus aL (agent13010.root+dsL) scalar13010.worldRadius world13010.frame
      agent13010.frame tm13010 ≤ -em13010 := by
  apply negative_check (lo := (68352283174587954183 / 100000000000000000000)) (hi := (8544035396823494273 / 12500000000000000000))
    (y := (-((4476999825526623819 / 6250000000000000000)))) (u := (3053417611522592821 / 6250000000000000000))
  · norm_num [world13010, agent13010, scalar13010, tp13010, tm13010, ep13010, em13010, dsL]
  · norm_num [world13010, agent13010, scalar13010, tp13010, tm13010, ep13010, em13010, dsL]
  · norm_num [world13010, agent13010, scalar13010, tp13010, tm13010, ep13010, em13010, dsL]
  · norm_num [world13010, agent13010, scalar13010, tp13010, tm13010, ep13010, em13010, dsL]
  · norm_num [world13010, agent13010, scalar13010, tp13010, tm13010, ep13010, em13010, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13010, agent13010, tp13010, tm13010, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13010, agent13010, tp13010, tm13010, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13010, agent13010, scalar13010, tp13010, tm13010, ep13010, em13010, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13010, agent13010, tp13010, tm13010, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13010, agent13010, scalar13010, tp13010, tm13010, ep13010, em13010, dsL]

theorem tails13010 :
    exp (-((13010:ℝ)*ep13010)) ≤ scalar13010.upperTail ∧
    exp (-((13010:ℝ)*em13010)) ≤ scalar13010.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13010:ℝ)) (by norm_num [ep13010]) ?_)
      (show bp13010^8 ≤ scalar13010.upperTail by norm_num [bp13010, scalar13010])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13010, bp13010, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13010:ℝ)) (by norm_num [em13010]) ?_)
      (show bm13010^8 ≤ scalar13010.lowerTail by norm_num [bm13010, scalar13010])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13010, bm13010, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13010 :
    agent13010.root+dsL+scalar13010.worldRadius < √(1/100/aL) ∧
    2*(agent13010.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13010, agent13010, scalar13010, tp13010, tm13010, ep13010, em13010, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13010, agent13010, scalar13010, tp13010, tm13010, ep13010, em13010, dsL]

noncomputable def master13010 : MasterCertificate 13010 world13010 agent13010 :=
  master scalar13010 dsL tp13010 tm13010 ep13010 em13010
    (by norm_num [dsL]) (by norm_num [tp13010]) (by norm_num [tm13010])
    (by norm_num [ep13010]) (by norm_num [em13010])
    positive13010 negative13010 tails13010.1 tails13010.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13010.1 tailGuards13010.2

theorem preserves13010 : master13010.toScalarCertificate = scalar13010 := rfl

noncomputable def tp13011 : ℝ := (1171837783 / 5000000000)
noncomputable def tm13011 : ℝ := (-((765370759 / 1250000000)))
noncomputable def ep13011 : ℝ := (52226831805788373 / 100000000000000000000)
noncomputable def em13011 : ℝ := (50804859917710883 / 100000000000000000000)
noncomputable def bp13011 : ℝ := (21383484455298688457 / 50000000000000000000)
noncomputable def bm13011 : ℝ := (43767548699094521191 / 100000000000000000000)

theorem positive13011 :
    Eplus aL (agent13011.root+dsL) scalar13011.worldRadius world13011.frame
      agent13011.frame tp13011 ≤ -ep13011 := by
  apply positive_check (eT := (7229888235714019391 / 6250000000000000000)) (y := (9517059928160296161 / 25000000000000000000)) (u := (36582069719537456123 / 25000000000000000000))
  · norm_num [world13011, agent13011, scalar13011, tp13011, tm13011, ep13011, em13011, dsL]
  · norm_num [world13011, agent13011, scalar13011, tp13011, tm13011, ep13011, em13011, dsL]
  · norm_num [world13011, agent13011, scalar13011, tp13011, tm13011, ep13011, em13011, dsL]
  · norm_num [world13011, agent13011, scalar13011, tp13011, tm13011, ep13011, em13011, dsL]
  · norm_num [world13011, agent13011, scalar13011, tp13011, tm13011, ep13011, em13011, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13011, agent13011, tp13011, tm13011, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13011, agent13011, scalar13011, tp13011, tm13011, ep13011, em13011, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13011, agent13011, tp13011, tm13011, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13011, agent13011, scalar13011, tp13011, tm13011, ep13011, em13011, dsL]

theorem negative13011 :
    Eminus aL (agent13011.root+dsL) scalar13011.worldRadius world13011.frame
      agent13011.frame tm13011 ≤ -em13011 := by
  apply negative_check (lo := (6835215561506844863 / 10000000000000000000)) (hi := (68352155615068448631 / 100000000000000000000))
    (y := (-((35815973698581550947 / 50000000000000000000)))) (u := (9770941223900303673 / 20000000000000000000))
  · norm_num [world13011, agent13011, scalar13011, tp13011, tm13011, ep13011, em13011, dsL]
  · norm_num [world13011, agent13011, scalar13011, tp13011, tm13011, ep13011, em13011, dsL]
  · norm_num [world13011, agent13011, scalar13011, tp13011, tm13011, ep13011, em13011, dsL]
  · norm_num [world13011, agent13011, scalar13011, tp13011, tm13011, ep13011, em13011, dsL]
  · norm_num [world13011, agent13011, scalar13011, tp13011, tm13011, ep13011, em13011, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13011, agent13011, tp13011, tm13011, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13011, agent13011, tp13011, tm13011, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13011, agent13011, scalar13011, tp13011, tm13011, ep13011, em13011, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13011, agent13011, tp13011, tm13011, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13011, agent13011, scalar13011, tp13011, tm13011, ep13011, em13011, dsL]

theorem tails13011 :
    exp (-((13011:ℝ)*ep13011)) ≤ scalar13011.upperTail ∧
    exp (-((13011:ℝ)*em13011)) ≤ scalar13011.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13011:ℝ)) (by norm_num [ep13011]) ?_)
      (show bp13011^8 ≤ scalar13011.upperTail by norm_num [bp13011, scalar13011])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13011, bp13011, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13011:ℝ)) (by norm_num [em13011]) ?_)
      (show bm13011^8 ≤ scalar13011.lowerTail by norm_num [bm13011, scalar13011])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13011, bm13011, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13011 :
    agent13011.root+dsL+scalar13011.worldRadius < √(1/100/aL) ∧
    2*(agent13011.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13011, agent13011, scalar13011, tp13011, tm13011, ep13011, em13011, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13011, agent13011, scalar13011, tp13011, tm13011, ep13011, em13011, dsL]

noncomputable def master13011 : MasterCertificate 13011 world13011 agent13011 :=
  master scalar13011 dsL tp13011 tm13011 ep13011 em13011
    (by norm_num [dsL]) (by norm_num [tp13011]) (by norm_num [tm13011])
    (by norm_num [ep13011]) (by norm_num [em13011])
    positive13011 negative13011 tails13011.1 tails13011.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13011.1 tailGuards13011.2

theorem preserves13011 : master13011.toScalarCertificate = scalar13011 := rfl

noncomputable def tp13012 : ℝ := (585937693 / 2500000000)
noncomputable def tm13012 : ℝ := (-((3061562759 / 5000000000)))
noncomputable def ep13012 : ℝ := (13057274488802139 / 25000000000000000000)
noncomputable def em13012 : ℝ := (12701696295869219 / 25000000000000000000)
noncomputable def bp13012 : ℝ := (42762600810270887127 / 100000000000000000000)
noncomputable def bm13012 : ℝ := (43763398834004080557 / 100000000000000000000)

theorem positive13012 :
    Eplus aL (agent13012.root+dsL) scalar13012.worldRadius world13012.frame
      agent13012.frame tp13012 ≤ -ep13012 := by
  apply positive_check (eT := (115678395109959071187 / 100000000000000000000)) (y := (19034461484556489329 / 50000000000000000000)) (u := (29265855735800184473 / 20000000000000000000))
  · norm_num [world13012, agent13012, scalar13012, tp13012, tm13012, ep13012, em13012, dsL]
  · norm_num [world13012, agent13012, scalar13012, tp13012, tm13012, ep13012, em13012, dsL]
  · norm_num [world13012, agent13012, scalar13012, tp13012, tm13012, ep13012, em13012, dsL]
  · norm_num [world13012, agent13012, scalar13012, tp13012, tm13012, ep13012, em13012, dsL]
  · norm_num [world13012, agent13012, scalar13012, tp13012, tm13012, ep13012, em13012, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13012, agent13012, tp13012, tm13012, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13012, agent13012, scalar13012, tp13012, tm13012, ep13012, em13012, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13012, agent13012, tp13012, tm13012, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13012, agent13012, scalar13012, tp13012, tm13012, ep13012, em13012, dsL]

theorem negative13012 :
    Eminus aL (agent13012.root+dsL) scalar13012.worldRadius world13012.frame
      agent13012.frame tm13012 ≤ -em13012 := by
  apply negative_check (lo := (68352029893049573069 / 100000000000000000000)) (hi := (6835202989304957307 / 10000000000000000000))
    (y := (-((14326378786301320063 / 20000000000000000000)))) (u := (48854732239997859821 / 100000000000000000000))
  · norm_num [world13012, agent13012, scalar13012, tp13012, tm13012, ep13012, em13012, dsL]
  · norm_num [world13012, agent13012, scalar13012, tp13012, tm13012, ep13012, em13012, dsL]
  · norm_num [world13012, agent13012, scalar13012, tp13012, tm13012, ep13012, em13012, dsL]
  · norm_num [world13012, agent13012, scalar13012, tp13012, tm13012, ep13012, em13012, dsL]
  · norm_num [world13012, agent13012, scalar13012, tp13012, tm13012, ep13012, em13012, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13012, agent13012, tp13012, tm13012, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13012, agent13012, tp13012, tm13012, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13012, agent13012, scalar13012, tp13012, tm13012, ep13012, em13012, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13012, agent13012, tp13012, tm13012, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13012, agent13012, scalar13012, tp13012, tm13012, ep13012, em13012, dsL]

theorem tails13012 :
    exp (-((13012:ℝ)*ep13012)) ≤ scalar13012.upperTail ∧
    exp (-((13012:ℝ)*em13012)) ≤ scalar13012.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13012:ℝ)) (by norm_num [ep13012]) ?_)
      (show bp13012^8 ≤ scalar13012.upperTail by norm_num [bp13012, scalar13012])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13012, bp13012, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13012:ℝ)) (by norm_num [em13012]) ?_)
      (show bm13012^8 ≤ scalar13012.lowerTail by norm_num [bm13012, scalar13012])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13012, bm13012, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13012 :
    agent13012.root+dsL+scalar13012.worldRadius < √(1/100/aL) ∧
    2*(agent13012.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13012, agent13012, scalar13012, tp13012, tm13012, ep13012, em13012, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13012, agent13012, scalar13012, tp13012, tm13012, ep13012, em13012, dsL]

noncomputable def master13012 : MasterCertificate 13012 world13012 agent13012 :=
  master scalar13012 dsL tp13012 tm13012 ep13012 em13012
    (by norm_num [dsL]) (by norm_num [tp13012]) (by norm_num [tm13012])
    (by norm_num [ep13012]) (by norm_num [em13012])
    positive13012 negative13012 tails13012.1 tails13012.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13012.1 tailGuards13012.2

theorem preserves13012 : master13012.toScalarCertificate = scalar13012 := rfl

noncomputable def tp13013 : ℝ := (468765167 / 2000000000)
noncomputable def tm13013 : ℝ := (-((6123285091 / 10000000000)))
noncomputable def ep13013 : ℝ := (52231362566475149 / 100000000000000000000)
noncomputable def em13013 : ℝ := (50808709031037887 / 100000000000000000000)
noncomputable def bp13013 : ℝ := (21379116991829685693 / 50000000000000000000)
noncomputable def bm13013 : ℝ := (43759250161243638783 / 100000000000000000000)

theorem positive13013 :
    Eplus aL (agent13013.root+dsL) scalar13013.worldRadius world13013.frame
      agent13013.frame tp13013 ≤ -ep13013 := by
  apply positive_check (eT := (115678577453623875981 / 100000000000000000000)) (y := (9517401012808901949 / 25000000000000000000)) (u := (2926605506099041879 / 2000000000000000000))
  · norm_num [world13013, agent13013, scalar13013, tp13013, tm13013, ep13013, em13013, dsL]
  · norm_num [world13013, agent13013, scalar13013, tp13013, tm13013, ep13013, em13013, dsL]
  · norm_num [world13013, agent13013, scalar13013, tp13013, tm13013, ep13013, em13013, dsL]
  · norm_num [world13013, agent13013, scalar13013, tp13013, tm13013, ep13013, em13013, dsL]
  · norm_num [world13013, agent13013, scalar13013, tp13013, tm13013, ep13013, em13013, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13013, agent13013, tp13013, tm13013, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13013, agent13013, scalar13013, tp13013, tm13013, ep13013, em13013, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13013, agent13013, tp13013, tm13013, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13013, agent13013, scalar13013, tp13013, tm13013, ep13013, em13013, dsL]

theorem negative13013 :
    Eminus aL (agent13013.root+dsL) scalar13013.worldRadius world13013.frame
      agent13013.frame tm13013 ≤ -em13013 := by
  apply negative_check (lo := (68351903574600185137 / 100000000000000000000)) (hi := (34175951787300092569 / 50000000000000000000))
    (y := (-((71631842033594817719 / 100000000000000000000)))) (u := (4885475759459027861 / 10000000000000000000))
  · norm_num [world13013, agent13013, scalar13013, tp13013, tm13013, ep13013, em13013, dsL]
  · norm_num [world13013, agent13013, scalar13013, tp13013, tm13013, ep13013, em13013, dsL]
  · norm_num [world13013, agent13013, scalar13013, tp13013, tm13013, ep13013, em13013, dsL]
  · norm_num [world13013, agent13013, scalar13013, tp13013, tm13013, ep13013, em13013, dsL]
  · norm_num [world13013, agent13013, scalar13013, tp13013, tm13013, ep13013, em13013, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13013, agent13013, tp13013, tm13013, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13013, agent13013, tp13013, tm13013, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13013, agent13013, scalar13013, tp13013, tm13013, ep13013, em13013, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13013, agent13013, tp13013, tm13013, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13013, agent13013, scalar13013, tp13013, tm13013, ep13013, em13013, dsL]

theorem tails13013 :
    exp (-((13013:ℝ)*ep13013)) ≤ scalar13013.upperTail ∧
    exp (-((13013:ℝ)*em13013)) ≤ scalar13013.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13013:ℝ)) (by norm_num [ep13013]) ?_)
      (show bp13013^8 ≤ scalar13013.upperTail by norm_num [bp13013, scalar13013])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13013, bp13013, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13013:ℝ)) (by norm_num [em13013]) ?_)
      (show bm13013^8 ≤ scalar13013.lowerTail by norm_num [bm13013, scalar13013])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13013, bm13013, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13013 :
    agent13013.root+dsL+scalar13013.worldRadius < √(1/100/aL) ∧
    2*(agent13013.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13013, agent13013, scalar13013, tp13013, tm13013, ep13013, em13013, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13013, agent13013, scalar13013, tp13013, tm13013, ep13013, em13013, dsL]

noncomputable def master13013 : MasterCertificate 13013 world13013 agent13013 :=
  master scalar13013 dsL tp13013 tm13013 ep13013 em13013
    (by norm_num [dsL]) (by norm_num [tp13013]) (by norm_num [tm13013])
    (by norm_num [ep13013]) (by norm_num [em13013])
    positive13013 negative13013 tails13013.1 tails13013.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13013.1 tailGuards13013.2

theorem preserves13013 : master13013.toScalarCertificate = scalar13013 := rfl

noncomputable def tp13014 : ℝ := (1171950479 / 5000000000)
noncomputable def tm13014 : ℝ := (-((122468893 / 200000000)))
noncomputable def ep13014 : ℝ := (3264601671717151 / 6250000000000000000)
noncomputable def em13014 : ℝ := (25405316223875939 / 50000000000000000000)
noncomputable def bp13014 : ℝ := (21376933830088525921 / 50000000000000000000)
noncomputable def bm13014 : ℝ := (21877550988996850191 / 50000000000000000000)

theorem positive13014 :
    Eplus aL (agent13014.root+dsL) scalar13014.worldRadius world13014.frame
      agent13014.frame tp13014 ≤ -ep13014 := by
  apply positive_check (eT := (115678760261619426703 / 100000000000000000000)) (y := (38070286556711574049 / 100000000000000000000)) (u := (9145704626281386689 / 6250000000000000000))
  · norm_num [world13014, agent13014, scalar13014, tp13014, tm13014, ep13014, em13014, dsL]
  · norm_num [world13014, agent13014, scalar13014, tp13014, tm13014, ep13014, em13014, dsL]
  · norm_num [world13014, agent13014, scalar13014, tp13014, tm13014, ep13014, em13014, dsL]
  · norm_num [world13014, agent13014, scalar13014, tp13014, tm13014, ep13014, em13014, dsL]
  · norm_num [world13014, agent13014, scalar13014, tp13014, tm13014, ep13014, em13014, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13014, agent13014, tp13014, tm13014, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13014, agent13014, scalar13014, tp13014, tm13014, ep13014, em13014, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13014, agent13014, tp13014, tm13014, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13014, agent13014, scalar13014, tp13014, tm13014, ep13014, em13014, dsL]

theorem negative13014 :
    Eminus aL (agent13014.root+dsL) scalar13014.worldRadius world13014.frame
      agent13014.frame tm13014 ≤ -em13014 := by
  apply negative_check (lo := (170879443146756099 / 250000000000000000)) (hi := (68351777258702439601 / 100000000000000000000))
    (y := (-((71631790892953465647 / 100000000000000000000)))) (u := (6106847822404129017 / 12500000000000000000))
  · norm_num [world13014, agent13014, scalar13014, tp13014, tm13014, ep13014, em13014, dsL]
  · norm_num [world13014, agent13014, scalar13014, tp13014, tm13014, ep13014, em13014, dsL]
  · norm_num [world13014, agent13014, scalar13014, tp13014, tm13014, ep13014, em13014, dsL]
  · norm_num [world13014, agent13014, scalar13014, tp13014, tm13014, ep13014, em13014, dsL]
  · norm_num [world13014, agent13014, scalar13014, tp13014, tm13014, ep13014, em13014, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13014, agent13014, tp13014, tm13014, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13014, agent13014, tp13014, tm13014, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13014, agent13014, scalar13014, tp13014, tm13014, ep13014, em13014, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13014, agent13014, tp13014, tm13014, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13014, agent13014, scalar13014, tp13014, tm13014, ep13014, em13014, dsL]

theorem tails13014 :
    exp (-((13014:ℝ)*ep13014)) ≤ scalar13014.upperTail ∧
    exp (-((13014:ℝ)*em13014)) ≤ scalar13014.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13014:ℝ)) (by norm_num [ep13014]) ?_)
      (show bp13014^8 ≤ scalar13014.upperTail by norm_num [bp13014, scalar13014])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13014, bp13014, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13014:ℝ)) (by norm_num [em13014]) ?_)
      (show bm13014^8 ≤ scalar13014.lowerTail by norm_num [bm13014, scalar13014])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13014, bm13014, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13014 :
    agent13014.root+dsL+scalar13014.worldRadius < √(1/100/aL) ∧
    2*(agent13014.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13014, agent13014, scalar13014, tp13014, tm13014, ep13014, em13014, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13014, agent13014, scalar13014, tp13014, tm13014, ep13014, em13014, dsL]

noncomputable def master13014 : MasterCertificate 13014 world13014 agent13014 :=
  master scalar13014 dsL tp13014 tm13014 ep13014 em13014
    (by norm_num [dsL]) (by norm_num [tp13014]) (by norm_num [tm13014])
    (by norm_num [ep13014]) (by norm_num [em13014])
    positive13014 negative13014 tails13014.1 tails13014.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13014.1 tailGuards13014.2

theorem preserves13014 : master13014.toScalarCertificate = scalar13014 := rfl

noncomputable def tp13015 : ℝ := (117198801 / 500000000)
noncomputable def tm13015 : ℝ := (-((1530900989 / 2500000000)))
noncomputable def ep13015 : ℝ := (1305897242741011 / 2500000000000000000)
noncomputable def em13015 : ℝ := (25406277390811589 / 50000000000000000000)
noncomputable def bp13015 : ℝ := (42749502388262427731 / 100000000000000000000)
noncomputable def bm13015 : ℝ := (21875477374166721089 / 50000000000000000000)

theorem positive13015 :
    Eplus aL (agent13015.root+dsL) scalar13015.worldRadius world13015.frame
      agent13015.frame tp13015 ≤ -ep13015 := by
  apply positive_check (eT := (57839471332103586747 / 50000000000000000000)) (y := (19035484058200865463 / 50000000000000000000)) (u := (146332271358878728083 / 100000000000000000000))
  · norm_num [world13015, agent13015, scalar13015, tp13015, tm13015, ep13015, em13015, dsL]
  · norm_num [world13015, agent13015, scalar13015, tp13015, tm13015, ep13015, em13015, dsL]
  · norm_num [world13015, agent13015, scalar13015, tp13015, tm13015, ep13015, em13015, dsL]
  · norm_num [world13015, agent13015, scalar13015, tp13015, tm13015, ep13015, em13015, dsL]
  · norm_num [world13015, agent13015, scalar13015, tp13015, tm13015, ep13015, em13015, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13015, agent13015, tp13015, tm13015, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13015, agent13015, scalar13015, tp13015, tm13015, ep13015, em13015, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13015, agent13015, tp13015, tm13015, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13015, agent13015, scalar13015, tp13015, tm13015, ep13015, em13015, dsL]

theorem negative13015 :
    Eminus aL (agent13015.root+dsL) scalar13015.worldRadius world13015.frame
      agent13015.frame tm13015 ≤ -em13015 := by
  apply negative_check (lo := (34175825980191158179 / 50000000000000000000)) (hi := (68351651960382316359 / 100000000000000000000))
    (y := (-((114610780007512747 / 160000000000000000)))) (u := (48854808661957362831 / 100000000000000000000))
  · norm_num [world13015, agent13015, scalar13015, tp13015, tm13015, ep13015, em13015, dsL]
  · norm_num [world13015, agent13015, scalar13015, tp13015, tm13015, ep13015, em13015, dsL]
  · norm_num [world13015, agent13015, scalar13015, tp13015, tm13015, ep13015, em13015, dsL]
  · norm_num [world13015, agent13015, scalar13015, tp13015, tm13015, ep13015, em13015, dsL]
  · norm_num [world13015, agent13015, scalar13015, tp13015, tm13015, ep13015, em13015, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13015, agent13015, tp13015, tm13015, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13015, agent13015, tp13015, tm13015, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13015, agent13015, scalar13015, tp13015, tm13015, ep13015, em13015, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13015, agent13015, tp13015, tm13015, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13015, agent13015, scalar13015, tp13015, tm13015, ep13015, em13015, dsL]

theorem tails13015 :
    exp (-((13015:ℝ)*ep13015)) ≤ scalar13015.upperTail ∧
    exp (-((13015:ℝ)*em13015)) ≤ scalar13015.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13015:ℝ)) (by norm_num [ep13015]) ?_)
      (show bp13015^8 ≤ scalar13015.upperTail by norm_num [bp13015, scalar13015])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13015, bp13015, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13015:ℝ)) (by norm_num [em13015]) ?_)
      (show bm13015^8 ≤ scalar13015.lowerTail by norm_num [bm13015, scalar13015])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13015, bm13015, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13015 :
    agent13015.root+dsL+scalar13015.worldRadius < √(1/100/aL) ∧
    2*(agent13015.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13015, agent13015, scalar13015, tp13015, tm13015, ep13015, em13015, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13015, agent13015, scalar13015, tp13015, tm13015, ep13015, em13015, dsL]

noncomputable def master13015 : MasterCertificate 13015 world13015 agent13015 :=
  master scalar13015 dsL tp13015 tm13015 ep13015 em13015
    (by norm_num [dsL]) (by norm_num [tp13015]) (by norm_num [tm13015])
    (by norm_num [ep13015]) (by norm_num [em13015])
    positive13015 negative13015 tails13015.1 tails13015.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13015.1 tailGuards13015.2

theorem preserves13015 : master13015.toScalarCertificate = scalar13015 := rfl

noncomputable def tp13016 : ℝ := (2344051023 / 10000000000)
noncomputable def tm13016 : ℝ := (-((6123763289 / 10000000000)))
noncomputable def ep13016 : ℝ := (6529768855764013 / 12500000000000000000)
noncomputable def em13016 : ℝ := (10162895079456869 / 20000000000000000000)
noncomputable def bp13016 : ℝ := (21372569294964754103 / 50000000000000000000)
noncomputable def bm13016 : ℝ := (5468351115559173581 / 12500000000000000000)

theorem positive13016 :
    Eplus aL (agent13016.root+dsL) scalar13016.worldRadius world13016.frame
      agent13016.frame tp13016 ≤ -ep13016 := by
  apply positive_check (eT := (115679124675712763393 / 100000000000000000000)) (y := (19035824636031908893 / 50000000000000000000)) (u := (4572914628525789641 / 3125000000000000000))
  · norm_num [world13016, agent13016, scalar13016, tp13016, tm13016, ep13016, em13016, dsL]
  · norm_num [world13016, agent13016, scalar13016, tp13016, tm13016, ep13016, em13016, dsL]
  · norm_num [world13016, agent13016, scalar13016, tp13016, tm13016, ep13016, em13016, dsL]
  · norm_num [world13016, agent13016, scalar13016, tp13016, tm13016, ep13016, em13016, dsL]
  · norm_num [world13016, agent13016, scalar13016, tp13016, tm13016, ep13016, em13016, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13016, agent13016, tp13016, tm13016, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13016, agent13016, scalar13016, tp13016, tm13016, ep13016, em13016, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13016, agent13016, tp13016, tm13016, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13016, agent13016, scalar13016, tp13016, tm13016, ep13016, em13016, dsL]

theorem negative13016 :
    Eminus aL (agent13016.root+dsL) scalar13016.worldRadius world13016.frame
      agent13016.frame tm13016 ≤ -em13016 := by
  apply negative_check (lo := (68351526490498995499 / 100000000000000000000)) (hi := (136703052980997991 / 200000000000000000))
    (y := (-((35815842647503208787 / 50000000000000000000)))) (u := (48854834168907709419 / 100000000000000000000))
  · norm_num [world13016, agent13016, scalar13016, tp13016, tm13016, ep13016, em13016, dsL]
  · norm_num [world13016, agent13016, scalar13016, tp13016, tm13016, ep13016, em13016, dsL]
  · norm_num [world13016, agent13016, scalar13016, tp13016, tm13016, ep13016, em13016, dsL]
  · norm_num [world13016, agent13016, scalar13016, tp13016, tm13016, ep13016, em13016, dsL]
  · norm_num [world13016, agent13016, scalar13016, tp13016, tm13016, ep13016, em13016, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13016, agent13016, tp13016, tm13016, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13016, agent13016, tp13016, tm13016, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13016, agent13016, scalar13016, tp13016, tm13016, ep13016, em13016, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13016, agent13016, tp13016, tm13016, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13016, agent13016, scalar13016, tp13016, tm13016, ep13016, em13016, dsL]

theorem tails13016 :
    exp (-((13016:ℝ)*ep13016)) ≤ scalar13016.upperTail ∧
    exp (-((13016:ℝ)*em13016)) ≤ scalar13016.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13016:ℝ)) (by norm_num [ep13016]) ?_)
      (show bp13016^8 ≤ scalar13016.upperTail by norm_num [bp13016, scalar13016])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13016, bp13016, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13016:ℝ)) (by norm_num [em13016]) ?_)
      (show bm13016^8 ≤ scalar13016.lowerTail by norm_num [bm13016, scalar13016])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13016, bm13016, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13016 :
    agent13016.root+dsL+scalar13016.worldRadius < √(1/100/aL) ∧
    2*(agent13016.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13016, agent13016, scalar13016, tp13016, tm13016, ep13016, em13016, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13016, agent13016, scalar13016, tp13016, tm13016, ep13016, em13016, dsL]

noncomputable def master13016 : MasterCertificate 13016 world13016 agent13016 :=
  master scalar13016 dsL tp13016 tm13016 ep13016 em13016
    (by norm_num [dsL]) (by norm_num [tp13016]) (by norm_num [tm13016])
    (by norm_num [ep13016]) (by norm_num [em13016])
    positive13016 negative13016 tails13016.1 tails13016.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13016.1 tailGuards13016.2

theorem preserves13016 : master13016.toScalarCertificate = scalar13016 := rfl

noncomputable def tp13017 : ℝ := (586031513 / 2500000000)
noncomputable def tm13017 : ℝ := (-((612392251 / 1000000000)))
noncomputable def ep13017 : ℝ := (5224041139910833 / 10000000000000000000)
noncomputable def em13017 : ℝ := (50816395479357787 / 100000000000000000000)
noncomputable def bp13017 : ℝ := (42740775401214639709 / 100000000000000000000)
noncomputable def bm13017 : ℝ := (2187133183160890769 / 5000000000000000000)

theorem positive13017 :
    Eplus aL (agent13017.root+dsL) scalar13017.worldRadius world13017.frame
      agent13017.frame tp13017 ≤ -ep13017 := by
  apply positive_check (eT := (115679306907175350337 / 100000000000000000000)) (y := (7614466220816445149 / 20000000000000000000)) (u := (73167132931651165881 / 50000000000000000000))
  · norm_num [world13017, agent13017, scalar13017, tp13017, tm13017, ep13017, em13017, dsL]
  · norm_num [world13017, agent13017, scalar13017, tp13017, tm13017, ep13017, em13017, dsL]
  · norm_num [world13017, agent13017, scalar13017, tp13017, tm13017, ep13017, em13017, dsL]
  · norm_num [world13017, agent13017, scalar13017, tp13017, tm13017, ep13017, em13017, dsL]
  · norm_num [world13017, agent13017, scalar13017, tp13017, tm13017, ep13017, em13017, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13017, agent13017, tp13017, tm13017, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13017, agent13017, scalar13017, tp13017, tm13017, ep13017, em13017, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13017, agent13017, tp13017, tm13017, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13017, agent13017, scalar13017, tp13017, tm13017, ep13017, em13017, dsL]

theorem negative13017 :
    Eminus aL (agent13017.root+dsL) scalar13017.worldRadius world13017.frame
      agent13017.frame tm13017 ≤ -em13017 := by
  apply negative_check (lo := (34175700719651243907 / 50000000000000000000)) (hi := (13670280287860497563 / 20000000000000000000))
    (y := (-((71631632610240096033 / 100000000000000000000)))) (u := (48854859907969708367 / 100000000000000000000))
  · norm_num [world13017, agent13017, scalar13017, tp13017, tm13017, ep13017, em13017, dsL]
  · norm_num [world13017, agent13017, scalar13017, tp13017, tm13017, ep13017, em13017, dsL]
  · norm_num [world13017, agent13017, scalar13017, tp13017, tm13017, ep13017, em13017, dsL]
  · norm_num [world13017, agent13017, scalar13017, tp13017, tm13017, ep13017, em13017, dsL]
  · norm_num [world13017, agent13017, scalar13017, tp13017, tm13017, ep13017, em13017, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13017, agent13017, tp13017, tm13017, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13017, agent13017, tp13017, tm13017, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13017, agent13017, scalar13017, tp13017, tm13017, ep13017, em13017, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13017, agent13017, tp13017, tm13017, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13017, agent13017, scalar13017, tp13017, tm13017, ep13017, em13017, dsL]

theorem tails13017 :
    exp (-((13017:ℝ)*ep13017)) ≤ scalar13017.upperTail ∧
    exp (-((13017:ℝ)*em13017)) ≤ scalar13017.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13017:ℝ)) (by norm_num [ep13017]) ?_)
      (show bp13017^8 ≤ scalar13017.upperTail by norm_num [bp13017, scalar13017])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13017, bp13017, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13017:ℝ)) (by norm_num [em13017]) ?_)
      (show bm13017^8 ≤ scalar13017.lowerTail by norm_num [bm13017, scalar13017])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13017, bm13017, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13017 :
    agent13017.root+dsL+scalar13017.worldRadius < √(1/100/aL) ∧
    2*(agent13017.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13017, agent13017, scalar13017, tp13017, tm13017, ep13017, em13017, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13017, agent13017, scalar13017, tp13017, tm13017, ep13017, em13017, dsL]

noncomputable def master13017 : MasterCertificate 13017 world13017 agent13017 :=
  master scalar13017 dsL tp13017 tm13017 ep13017 em13017
    (by norm_num [dsL]) (by norm_num [tp13017]) (by norm_num [tm13017])
    (by norm_num [ep13017]) (by norm_num [em13017])
    positive13017 negative13017 tails13017.1 tails13017.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13017.1 tailGuards13017.2

theorem preserves13017 : master13017.toScalarCertificate = scalar13017 := rfl

noncomputable def tp13018 : ℝ := (468840197 / 2000000000)
noncomputable def tm13018 : ℝ := (-((6124081689 / 10000000000)))
noncomputable def ep13018 : ℝ := (10448534082811827 / 20000000000000000000)
noncomputable def em13018 : ℝ := (3176144633966443 / 6250000000000000000)
noncomputable def bp13018 : ℝ := (42736413485950552191 / 100000000000000000000)
noncomputable def bm13018 : ℝ := (8747703918802660891 / 20000000000000000000)

theorem positive13018 :
    Eplus aL (agent13018.root+dsL) scalar13018.worldRadius world13018.frame
      agent13018.frame tp13018 ≤ -ep13018 := by
  apply positive_check (eT := (23135897696330609343 / 20000000000000000000)) (y := (19036505790803707409 / 50000000000000000000)) (u := (4572976926202537227 / 3125000000000000000))
  · norm_num [world13018, agent13018, scalar13018, tp13018, tm13018, ep13018, em13018, dsL]
  · norm_num [world13018, agent13018, scalar13018, tp13018, tm13018, ep13018, em13018, dsL]
  · norm_num [world13018, agent13018, scalar13018, tp13018, tm13018, ep13018, em13018, dsL]
  · norm_num [world13018, agent13018, scalar13018, tp13018, tm13018, ep13018, em13018, dsL]
  · norm_num [world13018, agent13018, scalar13018, tp13018, tm13018, ep13018, em13018, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13018, agent13018, tp13018, tm13018, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13018, agent13018, scalar13018, tp13018, tm13018, ep13018, em13018, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13018, agent13018, tp13018, tm13018, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13018, agent13018, scalar13018, tp13018, tm13018, ep13018, em13018, dsL]

theorem negative13018 :
    Eminus aL (agent13018.root+dsL) scalar13018.worldRadius world13018.frame
      agent13018.frame tm13018 ≤ -em13018 := by
  apply negative_check (lo := (34175638254777261633 / 50000000000000000000)) (hi := (68351276509554523267 / 100000000000000000000))
    (y := (-((71631579867349792913 / 100000000000000000000)))) (u := (3053430354715104539 / 6250000000000000000))
  · norm_num [world13018, agent13018, scalar13018, tp13018, tm13018, ep13018, em13018, dsL]
  · norm_num [world13018, agent13018, scalar13018, tp13018, tm13018, ep13018, em13018, dsL]
  · norm_num [world13018, agent13018, scalar13018, tp13018, tm13018, ep13018, em13018, dsL]
  · norm_num [world13018, agent13018, scalar13018, tp13018, tm13018, ep13018, em13018, dsL]
  · norm_num [world13018, agent13018, scalar13018, tp13018, tm13018, ep13018, em13018, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13018, agent13018, tp13018, tm13018, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13018, agent13018, tp13018, tm13018, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13018, agent13018, scalar13018, tp13018, tm13018, ep13018, em13018, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13018, agent13018, tp13018, tm13018, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13018, agent13018, scalar13018, tp13018, tm13018, ep13018, em13018, dsL]

theorem tails13018 :
    exp (-((13018:ℝ)*ep13018)) ≤ scalar13018.upperTail ∧
    exp (-((13018:ℝ)*em13018)) ≤ scalar13018.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13018:ℝ)) (by norm_num [ep13018]) ?_)
      (show bp13018^8 ≤ scalar13018.upperTail by norm_num [bp13018, scalar13018])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13018, bp13018, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13018:ℝ)) (by norm_num [em13018]) ?_)
      (show bm13018^8 ≤ scalar13018.lowerTail by norm_num [bm13018, scalar13018])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13018, bm13018, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13018 :
    agent13018.root+dsL+scalar13018.worldRadius < √(1/100/aL) ∧
    2*(agent13018.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13018, agent13018, scalar13018, tp13018, tm13018, ep13018, em13018, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13018, agent13018, scalar13018, tp13018, tm13018, ep13018, em13018, dsL]

noncomputable def master13018 : MasterCertificate 13018 world13018 agent13018 :=
  master scalar13018 dsL tp13018 tm13018 ep13018 em13018
    (by norm_num [dsL]) (by norm_num [tp13018]) (by norm_num [tm13018])
    (by norm_num [ep13018]) (by norm_num [em13018])
    positive13018 negative13018 tails13018.1 tails13018.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13018.1 tailGuards13018.2

theorem preserves13018 : master13018.toScalarCertificate = scalar13018 := rfl

noncomputable def tp13019 : ℝ := (234427593 / 1000000000)
noncomputable def tm13019 : ℝ := (-((3062120341 / 5000000000)))
noncomputable def ep13019 : ℝ := (1632654026425309 / 3125000000000000000)
noncomputable def em13019 : ℝ := (50820232274110401 / 100000000000000000000)
noncomputable def bp13019 : ℝ := (8546410436042815487 / 20000000000000000000)
noncomputable def bm13019 : ℝ := (10933594021825605287 / 25000000000000000000)

theorem positive13019 :
    Eplus aL (agent13019.root+dsL) scalar13019.worldRadius world13019.frame
      agent13019.frame tp13019 ≤ -ep13019 := by
  apply positive_check (eT := (28919917543865042417 / 25000000000000000000)) (y := (38073692490921806571 / 100000000000000000000)) (u := (146336258052300260627 / 100000000000000000000))
  · norm_num [world13019, agent13019, scalar13019, tp13019, tm13019, ep13019, em13019, dsL]
  · norm_num [world13019, agent13019, scalar13019, tp13019, tm13019, ep13019, em13019, dsL]
  · norm_num [world13019, agent13019, scalar13019, tp13019, tm13019, ep13019, em13019, dsL]
  · norm_num [world13019, agent13019, scalar13019, tp13019, tm13019, ep13019, em13019, dsL]
  · norm_num [world13019, agent13019, scalar13019, tp13019, tm13019, ep13019, em13019, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13019, agent13019, tp13019, tm13019, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13019, agent13019, scalar13019, tp13019, tm13019, ep13019, em13019, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13019, agent13019, tp13019, tm13019, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13019, agent13019, scalar13019, tp13019, tm13019, ep13019, em13019, dsL]

theorem negative13019 :
    Eminus aL (agent13019.root+dsL) scalar13019.worldRadius world13019.frame
      agent13019.frame tm13019 ≤ -em13019 := by
  apply negative_check (lo := (68351152312733561021 / 100000000000000000000)) (hi := (34175576156366780511 / 50000000000000000000))
    (y := (-((35815762968866409201 / 50000000000000000000)))) (u := (48854912022701495213 / 100000000000000000000))
  · norm_num [world13019, agent13019, scalar13019, tp13019, tm13019, ep13019, em13019, dsL]
  · norm_num [world13019, agent13019, scalar13019, tp13019, tm13019, ep13019, em13019, dsL]
  · norm_num [world13019, agent13019, scalar13019, tp13019, tm13019, ep13019, em13019, dsL]
  · norm_num [world13019, agent13019, scalar13019, tp13019, tm13019, ep13019, em13019, dsL]
  · norm_num [world13019, agent13019, scalar13019, tp13019, tm13019, ep13019, em13019, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13019, agent13019, tp13019, tm13019, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13019, agent13019, tp13019, tm13019, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13019, agent13019, scalar13019, tp13019, tm13019, ep13019, em13019, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13019, agent13019, tp13019, tm13019, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13019, agent13019, scalar13019, tp13019, tm13019, ep13019, em13019, dsL]

theorem tails13019 :
    exp (-((13019:ℝ)*ep13019)) ≤ scalar13019.upperTail ∧
    exp (-((13019:ℝ)*em13019)) ≤ scalar13019.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13019:ℝ)) (by norm_num [ep13019]) ?_)
      (show bp13019^8 ≤ scalar13019.upperTail by norm_num [bp13019, scalar13019])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13019, bp13019, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13019:ℝ)) (by norm_num [em13019]) ?_)
      (show bm13019^8 ≤ scalar13019.lowerTail by norm_num [bm13019, scalar13019])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13019, bm13019, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13019 :
    agent13019.root+dsL+scalar13019.worldRadius < √(1/100/aL) ∧
    2*(agent13019.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13019, agent13019, scalar13019, tp13019, tm13019, ep13019, em13019, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13019, agent13019, scalar13019, tp13019, tm13019, ep13019, em13019, dsL]

noncomputable def master13019 : MasterCertificate 13019 world13019 agent13019 :=
  master scalar13019 dsL tp13019 tm13019 ep13019 em13019
    (by norm_num [dsL]) (by norm_num [tp13019]) (by norm_num [tm13019])
    (by norm_num [ep13019]) (by norm_num [em13019])
    positive13019 negative13019 tails13019.1 tails13019.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13019.1 tailGuards13019.2

theorem preserves13019 : master13019.toScalarCertificate = scalar13019 := rfl

noncomputable def tp13020 : ℝ := (2344422481 / 10000000000)
noncomputable def tm13020 : ℝ := (-((1224923337 / 2000000000)))
noncomputable def ep13020 : ℝ := (10449708094841607 / 20000000000000000000)
noncomputable def em13020 : ℝ := (50823627822202537 / 100000000000000000000)
noncomputable def bp13020 : ℝ := (21363375042342456511 / 50000000000000000000)
noncomputable def bm13020 : ℝ := (10932295320993513563 / 25000000000000000000)

theorem positive13020 :
    Eplus aL (agent13020.root+dsL) scalar13020.worldRadius world13020.frame
      agent13020.frame tp13020 ≤ -ep13020 := by
  apply positive_check (eT := (115680366555545246289 / 100000000000000000000)) (y := (38073658341739479431 / 100000000000000000000)) (u := (29267241615934644051 / 20000000000000000000))
  · norm_num [world13020, agent13020, scalar13020, tp13020, tm13020, ep13020, em13020, dsL]
  · norm_num [world13020, agent13020, scalar13020, tp13020, tm13020, ep13020, em13020, dsL]
  · norm_num [world13020, agent13020, scalar13020, tp13020, tm13020, ep13020, em13020, dsL]
  · norm_num [world13020, agent13020, scalar13020, tp13020, tm13020, ep13020, em13020, dsL]
  · norm_num [world13020, agent13020, scalar13020, tp13020, tm13020, ep13020, em13020, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13020, agent13020, tp13020, tm13020, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13020, agent13020, scalar13020, tp13020, tm13020, ep13020, em13020, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13020, agent13020, tp13020, tm13020, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13020, agent13020, scalar13020, tp13020, tm13020, ep13020, em13020, dsL]

theorem negative13020 :
    Eminus aL (agent13020.root+dsL) scalar13020.worldRadius world13020.frame
      agent13020.frame tm13020 ≤ -em13020 := by
  apply negative_check (lo := (854376331107957301 / 1250000000000000000)) (hi := (68350106488636584081 / 100000000000000000000))
    (y := (-((71629604174839768737 / 100000000000000000000)))) (u := (9771170181458743701 / 20000000000000000000))
  · norm_num [world13020, agent13020, scalar13020, tp13020, tm13020, ep13020, em13020, dsL]
  · norm_num [world13020, agent13020, scalar13020, tp13020, tm13020, ep13020, em13020, dsL]
  · norm_num [world13020, agent13020, scalar13020, tp13020, tm13020, ep13020, em13020, dsL]
  · norm_num [world13020, agent13020, scalar13020, tp13020, tm13020, ep13020, em13020, dsL]
  · norm_num [world13020, agent13020, scalar13020, tp13020, tm13020, ep13020, em13020, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13020, agent13020, tp13020, tm13020, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13020, agent13020, tp13020, tm13020, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13020, agent13020, scalar13020, tp13020, tm13020, ep13020, em13020, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13020, agent13020, tp13020, tm13020, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13020, agent13020, scalar13020, tp13020, tm13020, ep13020, em13020, dsL]

theorem tails13020 :
    exp (-((13020:ℝ)*ep13020)) ≤ scalar13020.upperTail ∧
    exp (-((13020:ℝ)*em13020)) ≤ scalar13020.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13020:ℝ)) (by norm_num [ep13020]) ?_)
      (show bp13020^8 ≤ scalar13020.upperTail by norm_num [bp13020, scalar13020])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13020, bp13020, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13020:ℝ)) (by norm_num [em13020]) ?_)
      (show bm13020^8 ≤ scalar13020.lowerTail by norm_num [bm13020, scalar13020])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13020, bm13020, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13020 :
    agent13020.root+dsL+scalar13020.worldRadius < √(1/100/aL) ∧
    2*(agent13020.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13020, agent13020, scalar13020, tp13020, tm13020, ep13020, em13020, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13020, agent13020, scalar13020, tp13020, tm13020, ep13020, em13020, dsL]

noncomputable def master13020 : MasterCertificate 13020 world13020 agent13020 :=
  master scalar13020 dsL tp13020 tm13020 ep13020 em13020
    (by norm_num [dsL]) (by norm_num [tp13020]) (by norm_num [tm13020])
    (by norm_num [ep13020]) (by norm_num [em13020])
    positive13020 negative13020 tails13020.1 tails13020.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13020.1 tailGuards13020.2

theorem preserves13020 : master13020.toScalarCertificate = scalar13020 := rfl

noncomputable def tp13021 : ℝ := (2344497353 / 10000000000)
noncomputable def tm13021 : ℝ := (-((3062387779 / 5000000000)))
noncomputable def ep13021 : ℝ := (52250796398460053 / 100000000000000000000)
noncomputable def em13021 : ℝ := (25412771795306537 / 50000000000000000000)
noncomputable def bp13021 : ℝ := (42722390953894193739 / 100000000000000000000)
noncomputable def bm13021 : ℝ := (21862519921484389053 / 50000000000000000000)

theorem positive13021 :
    Eplus aL (agent13021.root+dsL) scalar13021.worldRadius world13021.frame
      agent13021.frame tp13021 ≤ -ep13021 := by
  apply positive_check (eT := (115680547780659205479 / 100000000000000000000)) (y := (11898230876726337 / 31250000000000000)) (u := (146337203847961167941 / 100000000000000000000))
  · norm_num [world13021, agent13021, scalar13021, tp13021, tm13021, ep13021, em13021, dsL]
  · norm_num [world13021, agent13021, scalar13021, tp13021, tm13021, ep13021, em13021, dsL]
  · norm_num [world13021, agent13021, scalar13021, tp13021, tm13021, ep13021, em13021, dsL]
  · norm_num [world13021, agent13021, scalar13021, tp13021, tm13021, ep13021, em13021, dsL]
  · norm_num [world13021, agent13021, scalar13021, tp13021, tm13021, ep13021, em13021, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13021, agent13021, tp13021, tm13021, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13021, agent13021, scalar13021, tp13021, tm13021, ep13021, em13021, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13021, agent13021, tp13021, tm13021, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13021, agent13021, scalar13021, tp13021, tm13021, ep13021, em13021, dsL]

theorem negative13021 :
    Eminus aL (agent13021.root+dsL) scalar13021.worldRadius world13021.frame
      agent13021.frame tm13021 ≤ -em13021 := by
  apply negative_check (lo := (68349982708716808473 / 100000000000000000000)) (hi := (34174991354358404237 / 50000000000000000000))
    (y := (-((4476846899925897101 / 6250000000000000000)))) (u := (24427938590017791701 / 50000000000000000000))
  · norm_num [world13021, agent13021, scalar13021, tp13021, tm13021, ep13021, em13021, dsL]
  · norm_num [world13021, agent13021, scalar13021, tp13021, tm13021, ep13021, em13021, dsL]
  · norm_num [world13021, agent13021, scalar13021, tp13021, tm13021, ep13021, em13021, dsL]
  · norm_num [world13021, agent13021, scalar13021, tp13021, tm13021, ep13021, em13021, dsL]
  · norm_num [world13021, agent13021, scalar13021, tp13021, tm13021, ep13021, em13021, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13021, agent13021, tp13021, tm13021, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13021, agent13021, tp13021, tm13021, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13021, agent13021, scalar13021, tp13021, tm13021, ep13021, em13021, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13021, agent13021, tp13021, tm13021, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13021, agent13021, scalar13021, tp13021, tm13021, ep13021, em13021, dsL]

theorem tails13021 :
    exp (-((13021:ℝ)*ep13021)) ≤ scalar13021.upperTail ∧
    exp (-((13021:ℝ)*em13021)) ≤ scalar13021.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13021:ℝ)) (by norm_num [ep13021]) ?_)
      (show bp13021^8 ≤ scalar13021.upperTail by norm_num [bp13021, scalar13021])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13021, bp13021, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13021:ℝ)) (by norm_num [em13021]) ?_)
      (show bm13021^8 ≤ scalar13021.lowerTail by norm_num [bm13021, scalar13021])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13021, bm13021, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13021 :
    agent13021.root+dsL+scalar13021.worldRadius < √(1/100/aL) ∧
    2*(agent13021.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13021, agent13021, scalar13021, tp13021, tm13021, ep13021, em13021, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13021, agent13021, scalar13021, tp13021, tm13021, ep13021, em13021, dsL]

noncomputable def master13021 : MasterCertificate 13021 world13021 agent13021 :=
  master scalar13021 dsL tp13021 tm13021 ep13021 em13021
    (by norm_num [dsL]) (by norm_num [tp13021]) (by norm_num [tm13021])
    (by norm_num [ep13021]) (by norm_num [em13021])
    positive13021 negative13021 tails13021.1 tails13021.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13021.1 tailGuards13021.2

theorem preserves13021 : master13021.toScalarCertificate = scalar13021 := rfl

noncomputable def tp13022 : ℝ := (1172286047 / 5000000000)
noncomputable def tm13022 : ℝ := (-((6124934389 / 10000000000)))
noncomputable def ep13022 : ℝ := (52253050969611277 / 100000000000000000000)
noncomputable def em13022 : ℝ := (50827458134447839 / 100000000000000000000)
noncomputable def bp13022 : ℝ := (21359016483892159581 / 50000000000000000000)
noncomputable def bm13022 : ℝ := (43720899456277490267 / 100000000000000000000)

theorem positive13022 :
    Eplus aL (agent13022.root+dsL) scalar13022.worldRadius world13022.frame
      agent13022.frame tp13022 ≤ -ep13022 := by
  apply positive_check (eT := (57840364048653591243 / 50000000000000000000)) (y := (38075017253515657679 / 100000000000000000000)) (u := (11707055733851937 / 8000000000000000))
  · norm_num [world13022, agent13022, scalar13022, tp13022, tm13022, ep13022, em13022, dsL]
  · norm_num [world13022, agent13022, scalar13022, tp13022, tm13022, ep13022, em13022, dsL]
  · norm_num [world13022, agent13022, scalar13022, tp13022, tm13022, ep13022, em13022, dsL]
  · norm_num [world13022, agent13022, scalar13022, tp13022, tm13022, ep13022, em13022, dsL]
  · norm_num [world13022, agent13022, scalar13022, tp13022, tm13022, ep13022, em13022, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13022, agent13022, tp13022, tm13022, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13022, agent13022, scalar13022, tp13022, tm13022, ep13022, em13022, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13022, agent13022, tp13022, tm13022, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13022, agent13022, scalar13022, tp13022, tm13022, ep13022, em13022, dsL]

theorem negative13022 :
    Eminus aL (agent13022.root+dsL) scalar13022.worldRadius world13022.frame
      agent13022.frame tm13022 ≤ -em13022 := by
  apply negative_check (lo := (68349859050214659219 / 100000000000000000000)) (hi := (3417492952510732961 / 5000000000000000000))
    (y := (-((35814748344277563337 / 50000000000000000000)))) (u := (48855903420660911349 / 100000000000000000000))
  · norm_num [world13022, agent13022, scalar13022, tp13022, tm13022, ep13022, em13022, dsL]
  · norm_num [world13022, agent13022, scalar13022, tp13022, tm13022, ep13022, em13022, dsL]
  · norm_num [world13022, agent13022, scalar13022, tp13022, tm13022, ep13022, em13022, dsL]
  · norm_num [world13022, agent13022, scalar13022, tp13022, tm13022, ep13022, em13022, dsL]
  · norm_num [world13022, agent13022, scalar13022, tp13022, tm13022, ep13022, em13022, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13022, agent13022, tp13022, tm13022, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13022, agent13022, tp13022, tm13022, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13022, agent13022, scalar13022, tp13022, tm13022, ep13022, em13022, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13022, agent13022, tp13022, tm13022, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13022, agent13022, scalar13022, tp13022, tm13022, ep13022, em13022, dsL]

theorem tails13022 :
    exp (-((13022:ℝ)*ep13022)) ≤ scalar13022.upperTail ∧
    exp (-((13022:ℝ)*em13022)) ≤ scalar13022.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13022:ℝ)) (by norm_num [ep13022]) ?_)
      (show bp13022^8 ≤ scalar13022.upperTail by norm_num [bp13022, scalar13022])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13022, bp13022, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13022:ℝ)) (by norm_num [em13022]) ?_)
      (show bm13022^8 ≤ scalar13022.lowerTail by norm_num [bm13022, scalar13022])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13022, bm13022, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13022 :
    agent13022.root+dsL+scalar13022.worldRadius < √(1/100/aL) ∧
    2*(agent13022.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13022, agent13022, scalar13022, tp13022, tm13022, ep13022, em13022, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13022, agent13022, scalar13022, tp13022, tm13022, ep13022, em13022, dsL]

noncomputable def master13022 : MasterCertificate 13022 world13022 agent13022 :=
  master scalar13022 dsL tp13022 tm13022 ep13022 em13022
    (by norm_num [dsL]) (by norm_num [tp13022]) (by norm_num [tm13022])
    (by norm_num [ep13022]) (by norm_num [em13022])
    positive13022 negative13022 tails13022.1 tails13022.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13022.1 tailGuards13022.2

theorem preserves13022 : master13022.toScalarCertificate = scalar13022 := rfl

noncomputable def tp13023 : ℝ := (1172323459 / 5000000000)
noncomputable def tm13023 : ℝ := (-((6125093013 / 10000000000)))
noncomputable def ep13023 : ℝ := (52255304480146541 / 100000000000000000000)
noncomputable def em13023 : ℝ := (10165874340558409 / 20000000000000000000)
noncomputable def bp13023 : ℝ := (1334802372591886269 / 3125000000000000000)
noncomputable def bm13023 : ℝ := (43716759946613175841 / 100000000000000000000)

theorem positive13023 :
    Eplus aL (agent13023.root+dsL) scalar13023.worldRadius world13023.frame
      agent13023.frame tp13023 ≤ -ep13023 := by
  apply positive_check (eT := (14460113630439558351 / 12500000000000000000)) (y := (38075697421103333583 / 100000000000000000000)) (u := (146339192021516387331 / 100000000000000000000))
  · norm_num [world13023, agent13023, scalar13023, tp13023, tm13023, ep13023, em13023, dsL]
  · norm_num [world13023, agent13023, scalar13023, tp13023, tm13023, ep13023, em13023, dsL]
  · norm_num [world13023, agent13023, scalar13023, tp13023, tm13023, ep13023, em13023, dsL]
  · norm_num [world13023, agent13023, scalar13023, tp13023, tm13023, ep13023, em13023, dsL]
  · norm_num [world13023, agent13023, scalar13023, tp13023, tm13023, ep13023, em13023, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13023, agent13023, tp13023, tm13023, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13023, agent13023, scalar13023, tp13023, tm13023, ep13023, em13023, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13023, agent13023, tp13023, tm13023, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13023, agent13023, scalar13023, tp13023, tm13023, ep13023, em13023, dsL]

theorem negative13023 :
    Eminus aL (agent13023.root+dsL) scalar13023.worldRadius world13023.frame
      agent13023.frame tm13023 ≤ -em13023 := by
  apply negative_check (lo := (68349736213801251373 / 100000000000000000000)) (hi := (34174868106900625687 / 50000000000000000000))
    (y := (-((7162944146129490187 / 10000000000000000000)))) (u := (24427965201222639653 / 50000000000000000000))
  · norm_num [world13023, agent13023, scalar13023, tp13023, tm13023, ep13023, em13023, dsL]
  · norm_num [world13023, agent13023, scalar13023, tp13023, tm13023, ep13023, em13023, dsL]
  · norm_num [world13023, agent13023, scalar13023, tp13023, tm13023, ep13023, em13023, dsL]
  · norm_num [world13023, agent13023, scalar13023, tp13023, tm13023, ep13023, em13023, dsL]
  · norm_num [world13023, agent13023, scalar13023, tp13023, tm13023, ep13023, em13023, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13023, agent13023, tp13023, tm13023, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13023, agent13023, tp13023, tm13023, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13023, agent13023, scalar13023, tp13023, tm13023, ep13023, em13023, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13023, agent13023, tp13023, tm13023, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13023, agent13023, scalar13023, tp13023, tm13023, ep13023, em13023, dsL]

theorem tails13023 :
    exp (-((13023:ℝ)*ep13023)) ≤ scalar13023.upperTail ∧
    exp (-((13023:ℝ)*em13023)) ≤ scalar13023.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13023:ℝ)) (by norm_num [ep13023]) ?_)
      (show bp13023^8 ≤ scalar13023.upperTail by norm_num [bp13023, scalar13023])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13023, bp13023, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13023:ℝ)) (by norm_num [em13023]) ?_)
      (show bm13023^8 ≤ scalar13023.lowerTail by norm_num [bm13023, scalar13023])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13023, bm13023, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13023 :
    agent13023.root+dsL+scalar13023.worldRadius < √(1/100/aL) ∧
    2*(agent13023.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13023, agent13023, scalar13023, tp13023, tm13023, ep13023, em13023, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13023, agent13023, scalar13023, tp13023, tm13023, ep13023, em13023, dsL]

noncomputable def master13023 : MasterCertificate 13023 world13023 agent13023 :=
  master scalar13023 dsL tp13023 tm13023 ep13023 em13023
    (by norm_num [dsL]) (by norm_num [tp13023]) (by norm_num [tm13023])
    (by norm_num [ep13023]) (by norm_num [em13023])
    positive13023 negative13023 tails13023.1 tails13023.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13023.1 tailGuards13023.2

theorem preserves13023 : master13023.toScalarCertificate = scalar13023 := rfl

noncomputable def tp13024 : ℝ := (1172360837 / 5000000000)
noncomputable def tm13024 : ℝ := (-((122505033 / 200000000)))
noncomputable def ep13024 : ℝ := (52257556313412219 / 100000000000000000000)
noncomputable def em13024 : ℝ := (50831283707146201 / 100000000000000000000)
noncomputable def bp13024 : ℝ := (4270932024809888279 / 10000000000000000000)
noncomputable def bm13024 : ℝ := (10928155433190377981 / 25000000000000000000)

theorem positive13024 :
    Eplus aL (agent13024.root+dsL) scalar13024.worldRadius world13024.frame
      agent13024.frame tp13024 ≤ -ep13024 := by
  apply positive_check (eT := (115681089534113216939 / 100000000000000000000)) (y := (38076376874630615851 / 100000000000000000000)) (u := (18292523291462038483 / 12500000000000000000))
  · norm_num [world13024, agent13024, scalar13024, tp13024, tm13024, ep13024, em13024, dsL]
  · norm_num [world13024, agent13024, scalar13024, tp13024, tm13024, ep13024, em13024, dsL]
  · norm_num [world13024, agent13024, scalar13024, tp13024, tm13024, ep13024, em13024, dsL]
  · norm_num [world13024, agent13024, scalar13024, tp13024, tm13024, ep13024, em13024, dsL]
  · norm_num [world13024, agent13024, scalar13024, tp13024, tm13024, ep13024, em13024, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13024, agent13024, tp13024, tm13024, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13024, agent13024, scalar13024, tp13024, tm13024, ep13024, em13024, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13024, agent13024, tp13024, tm13024, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13024, agent13024, scalar13024, tp13024, tm13024, ep13024, em13024, dsL]

theorem negative13024 :
    Eminus aL (agent13024.root+dsL) scalar13024.worldRadius world13024.frame
      agent13024.frame tm13024 ≤ -em13024 := by
  apply negative_check (lo := (68349613265150160263 / 100000000000000000000)) (hi := (8543701658143770033 / 12500000000000000000))
    (y := (-((4476836686855389309 / 6250000000000000000)))) (u := (48855957015063749803 / 100000000000000000000))
  · norm_num [world13024, agent13024, scalar13024, tp13024, tm13024, ep13024, em13024, dsL]
  · norm_num [world13024, agent13024, scalar13024, tp13024, tm13024, ep13024, em13024, dsL]
  · norm_num [world13024, agent13024, scalar13024, tp13024, tm13024, ep13024, em13024, dsL]
  · norm_num [world13024, agent13024, scalar13024, tp13024, tm13024, ep13024, em13024, dsL]
  · norm_num [world13024, agent13024, scalar13024, tp13024, tm13024, ep13024, em13024, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13024, agent13024, tp13024, tm13024, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13024, agent13024, tp13024, tm13024, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13024, agent13024, scalar13024, tp13024, tm13024, ep13024, em13024, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13024, agent13024, tp13024, tm13024, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13024, agent13024, scalar13024, tp13024, tm13024, ep13024, em13024, dsL]

theorem tails13024 :
    exp (-((13024:ℝ)*ep13024)) ≤ scalar13024.upperTail ∧
    exp (-((13024:ℝ)*em13024)) ≤ scalar13024.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13024:ℝ)) (by norm_num [ep13024]) ?_)
      (show bp13024^8 ≤ scalar13024.upperTail by norm_num [bp13024, scalar13024])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13024, bp13024, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13024:ℝ)) (by norm_num [em13024]) ?_)
      (show bm13024^8 ≤ scalar13024.lowerTail by norm_num [bm13024, scalar13024])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13024, bm13024, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13024 :
    agent13024.root+dsL+scalar13024.worldRadius < √(1/100/aL) ∧
    2*(agent13024.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13024, agent13024, scalar13024, tp13024, tm13024, ep13024, em13024, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13024, agent13024, scalar13024, tp13024, tm13024, ep13024, em13024, dsL]

noncomputable def master13024 : MasterCertificate 13024 world13024 agent13024 :=
  master scalar13024 dsL tp13024 tm13024 ep13024 em13024
    (by norm_num [dsL]) (by norm_num [tp13024]) (by norm_num [tm13024])
    (by norm_num [ep13024]) (by norm_num [em13024])
    positive13024 negative13024 tails13024.1 tails13024.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13024.1 tailGuards13024.2

theorem preserves13024 : master13024.toScalarCertificate = scalar13024 := rfl

end BstLean.Part268
