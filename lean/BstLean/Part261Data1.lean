import BstLean.Part261Checker
import BstLean.Part259Data5
import BstLean.Part259Data6
import BstLean.Part259Data7
import BstLean.Part259Data8
import BstLean.Part259Data9

namespace BstLean.Part261
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part259

noncomputable def tp12250 : ℝ := (575951723 / 2500000000)
noncomputable def tm12250 : ℝ := (-((6061453 / 10000000)))
noncomputable def ep12250 : ℝ := (50671196003428449 / 100000000000000000000)
noncomputable def em12250 : ℝ := (24794670819922497 / 50000000000000000000)
noncomputable def bp12250 : ℝ := (5753601206246094323 / 12500000000000000000)
noncomputable def bm12250 : ℝ := (9359533782564272679 / 20000000000000000000)

theorem positive12250 :
    Eplus aL (agent12250.root+dsL) scalar12250.worldRadius world12250.frame
      agent12250.frame tp12250 ≤ -ep12250 := by
  apply positive_check (eT := (115675809473180995201 / 100000000000000000000)) (y := (37169705536784689973 / 100000000000000000000)) (u := (72509679318888888267 / 50000000000000000000))
  · norm_num [world12250, agent12250, scalar12250, tp12250, tm12250, ep12250, em12250, dsL]
  · norm_num [world12250, agent12250, scalar12250, tp12250, tm12250, ep12250, em12250, dsL]
  · norm_num [world12250, agent12250, scalar12250, tp12250, tm12250, ep12250, em12250, dsL]
  · norm_num [world12250, agent12250, scalar12250, tp12250, tm12250, ep12250, em12250, dsL]
  · norm_num [world12250, agent12250, scalar12250, tp12250, tm12250, ep12250, em12250, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12250, agent12250, tp12250, tm12250, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12250, agent12250, scalar12250, tp12250, tm12250, ep12250, em12250, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12250, agent12250, tp12250, tm12250, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12250, agent12250, scalar12250, tp12250, tm12250, ep12250, em12250, dsL]

theorem negative12250 :
    Eminus aL (agent12250.root+dsL) scalar12250.worldRadius world12250.frame
      agent12250.frame tm12250 ≤ -em12250 := by
  apply negative_check (lo := (68171852464556442951 / 100000000000000000000)) (hi := (8521481558069555369 / 12500000000000000000))
    (y := (-((35425603160448731083 / 50000000000000000000)))) (u := (24618813872988872877 / 50000000000000000000))
  · norm_num [world12250, agent12250, scalar12250, tp12250, tm12250, ep12250, em12250, dsL]
  · norm_num [world12250, agent12250, scalar12250, tp12250, tm12250, ep12250, em12250, dsL]
  · norm_num [world12250, agent12250, scalar12250, tp12250, tm12250, ep12250, em12250, dsL]
  · norm_num [world12250, agent12250, scalar12250, tp12250, tm12250, ep12250, em12250, dsL]
  · norm_num [world12250, agent12250, scalar12250, tp12250, tm12250, ep12250, em12250, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12250, agent12250, tp12250, tm12250, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12250, agent12250, tp12250, tm12250, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12250, agent12250, scalar12250, tp12250, tm12250, ep12250, em12250, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12250, agent12250, tp12250, tm12250, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12250, agent12250, scalar12250, tp12250, tm12250, ep12250, em12250, dsL]

theorem tails12250 :
    exp (-((12250:ℝ)*ep12250)) ≤ scalar12250.upperTail ∧
    exp (-((12250:ℝ)*em12250)) ≤ scalar12250.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12250:ℝ)) (by norm_num [ep12250]) ?_)
      (show bp12250^8 ≤ scalar12250.upperTail by norm_num [bp12250, scalar12250])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12250, bp12250, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12250:ℝ)) (by norm_num [em12250]) ?_)
      (show bm12250^8 ≤ scalar12250.lowerTail by norm_num [bm12250, scalar12250])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12250, bm12250, Finset.sum_range_succ, Nat.factorial]

theorem guards12250 :
    agent12250.root+dsL+scalar12250.worldRadius < √(1/100/aL) ∧
    2*(agent12250.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12250, agent12250, scalar12250, tp12250, tm12250, ep12250, em12250, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12250, agent12250, scalar12250, tp12250, tm12250, ep12250, em12250, dsL]

noncomputable def master12250 : MasterCertificate 12250 world12250 agent12250 :=
  master scalar12250 dsL tp12250 tm12250 ep12250 em12250
    (by norm_num [dsL]) (by norm_num [tp12250]) (by norm_num [tm12250])
    (by norm_num [ep12250]) (by norm_num [em12250])
    positive12250 negative12250 tails12250.1 tails12250.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12250.1 guards12250.2

theorem preserves12250 : master12250.toScalarCertificate = scalar12250 := rfl

noncomputable def tp12251 : ℝ := (2303909639 / 10000000000)
noncomputable def tm12251 : ℝ := (-((1212336353 / 2000000000)))
noncomputable def ep12251 : ℝ := (12668578570348269 / 25000000000000000000)
noncomputable def em12251 : ℝ := (495920721435751 / 1000000000000000000)
noncomputable def bp12251 : ℝ := (5752962065420760807 / 12500000000000000000)
noncomputable def bm12251 : ℝ := (23396405761719758081 / 50000000000000000000)

theorem positive12251 :
    Eplus aL (agent12251.root+dsL) scalar12251.worldRadius world12251.frame
      agent12251.frame tp12251 ≤ -ep12251 := by
  apply positive_check (eT := (3614880111797553359 / 3125000000000000000)) (y := (37170554057681010903 / 100000000000000000000)) (u := (145020589162560151243 / 100000000000000000000))
  · norm_num [world12251, agent12251, scalar12251, tp12251, tm12251, ep12251, em12251, dsL]
  · norm_num [world12251, agent12251, scalar12251, tp12251, tm12251, ep12251, em12251, dsL]
  · norm_num [world12251, agent12251, scalar12251, tp12251, tm12251, ep12251, em12251, dsL]
  · norm_num [world12251, agent12251, scalar12251, tp12251, tm12251, ep12251, em12251, dsL]
  · norm_num [world12251, agent12251, scalar12251, tp12251, tm12251, ep12251, em12251, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12251, agent12251, tp12251, tm12251, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12251, agent12251, scalar12251, tp12251, tm12251, ep12251, em12251, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12251, agent12251, tp12251, tm12251, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12251, agent12251, scalar12251, tp12251, tm12251, ep12251, em12251, dsL]

theorem negative12251 :
    Eminus aL (agent12251.root+dsL) scalar12251.worldRadius world12251.frame
      agent12251.frame tm12251 ≤ -em12251 := by
  apply negative_check (lo := (68171482517943797963 / 100000000000000000000)) (hi := (17042870629485949491 / 25000000000000000000))
    (y := (-((70851286960068357509 / 100000000000000000000)))) (u := (1969503521647158867 / 4000000000000000000))
  · norm_num [world12251, agent12251, scalar12251, tp12251, tm12251, ep12251, em12251, dsL]
  · norm_num [world12251, agent12251, scalar12251, tp12251, tm12251, ep12251, em12251, dsL]
  · norm_num [world12251, agent12251, scalar12251, tp12251, tm12251, ep12251, em12251, dsL]
  · norm_num [world12251, agent12251, scalar12251, tp12251, tm12251, ep12251, em12251, dsL]
  · norm_num [world12251, agent12251, scalar12251, tp12251, tm12251, ep12251, em12251, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12251, agent12251, tp12251, tm12251, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12251, agent12251, tp12251, tm12251, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12251, agent12251, scalar12251, tp12251, tm12251, ep12251, em12251, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12251, agent12251, tp12251, tm12251, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12251, agent12251, scalar12251, tp12251, tm12251, ep12251, em12251, dsL]

theorem tails12251 :
    exp (-((12251:ℝ)*ep12251)) ≤ scalar12251.upperTail ∧
    exp (-((12251:ℝ)*em12251)) ≤ scalar12251.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12251:ℝ)) (by norm_num [ep12251]) ?_)
      (show bp12251^8 ≤ scalar12251.upperTail by norm_num [bp12251, scalar12251])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12251, bp12251, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12251:ℝ)) (by norm_num [em12251]) ?_)
      (show bm12251^8 ≤ scalar12251.lowerTail by norm_num [bm12251, scalar12251])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12251, bm12251, Finset.sum_range_succ, Nat.factorial]

theorem guards12251 :
    agent12251.root+dsL+scalar12251.worldRadius < √(1/100/aL) ∧
    2*(agent12251.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12251, agent12251, scalar12251, tp12251, tm12251, ep12251, em12251, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12251, agent12251, scalar12251, tp12251, tm12251, ep12251, em12251, dsL]

noncomputable def master12251 : MasterCertificate 12251 world12251 agent12251 :=
  master scalar12251 dsL tp12251 tm12251 ep12251 em12251
    (by norm_num [dsL]) (by norm_num [tp12251]) (by norm_num [tm12251])
    (by norm_num [ep12251]) (by norm_num [em12251])
    positive12251 negative12251 tails12251.1 tails12251.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12251.1 guards12251.2

theorem preserves12251 : master12251.toScalarCertificate = scalar12251 := rfl

noncomputable def tp12252 : ℝ := (2304012383 / 10000000000)
noncomputable def tm12252 : ℝ := (-((6061910227 / 10000000000)))
noncomputable def ep12252 : ℝ := (5067743078428063 / 10000000000000000000)
noncomputable def em12252 : ℝ := (49594801011243851 / 100000000000000000000)
noncomputable def bp12252 : ℝ := (46018584857039321469 / 100000000000000000000)
noncomputable def bm12252 : ℝ := (46787955491178401557 / 100000000000000000000)

theorem positive12252 :
    Eplus aL (agent12252.root+dsL) scalar12252.worldRadius world12252.frame
      agent12252.frame tp12252 ≤ -ep12252 := by
  apply positive_check (eT := (115676517692164694489 / 100000000000000000000)) (y := (9292850719179608641 / 25000000000000000000)) (u := (18127727516269185407 / 12500000000000000000))
  · norm_num [world12252, agent12252, scalar12252, tp12252, tm12252, ep12252, em12252, dsL]
  · norm_num [world12252, agent12252, scalar12252, tp12252, tm12252, ep12252, em12252, dsL]
  · norm_num [world12252, agent12252, scalar12252, tp12252, tm12252, ep12252, em12252, dsL]
  · norm_num [world12252, agent12252, scalar12252, tp12252, tm12252, ep12252, em12252, dsL]
  · norm_num [world12252, agent12252, scalar12252, tp12252, tm12252, ep12252, em12252, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12252, agent12252, tp12252, tm12252, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12252, agent12252, scalar12252, tp12252, tm12252, ep12252, em12252, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12252, agent12252, tp12252, tm12252, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12252, agent12252, scalar12252, tp12252, tm12252, ep12252, em12252, dsL]

theorem negative12252 :
    Eminus aL (agent12252.root+dsL) scalar12252.worldRadius world12252.frame
      agent12252.frame tm12252 ≤ -em12252 := by
  apply negative_check (lo := (8521389227770560151 / 12500000000000000000)) (hi := (68171113822164481209 / 100000000000000000000))
    (y := (-((70851365106227710117 / 100000000000000000000)))) (u := (4923754956390999389 / 10000000000000000000))
  · norm_num [world12252, agent12252, scalar12252, tp12252, tm12252, ep12252, em12252, dsL]
  · norm_num [world12252, agent12252, scalar12252, tp12252, tm12252, ep12252, em12252, dsL]
  · norm_num [world12252, agent12252, scalar12252, tp12252, tm12252, ep12252, em12252, dsL]
  · norm_num [world12252, agent12252, scalar12252, tp12252, tm12252, ep12252, em12252, dsL]
  · norm_num [world12252, agent12252, scalar12252, tp12252, tm12252, ep12252, em12252, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12252, agent12252, tp12252, tm12252, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12252, agent12252, tp12252, tm12252, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12252, agent12252, scalar12252, tp12252, tm12252, ep12252, em12252, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12252, agent12252, tp12252, tm12252, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12252, agent12252, scalar12252, tp12252, tm12252, ep12252, em12252, dsL]

theorem tails12252 :
    exp (-((12252:ℝ)*ep12252)) ≤ scalar12252.upperTail ∧
    exp (-((12252:ℝ)*em12252)) ≤ scalar12252.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12252:ℝ)) (by norm_num [ep12252]) ?_)
      (show bp12252^8 ≤ scalar12252.upperTail by norm_num [bp12252, scalar12252])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12252, bp12252, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12252:ℝ)) (by norm_num [em12252]) ?_)
      (show bm12252^8 ≤ scalar12252.lowerTail by norm_num [bm12252, scalar12252])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12252, bm12252, Finset.sum_range_succ, Nat.factorial]

theorem guards12252 :
    agent12252.root+dsL+scalar12252.worldRadius < √(1/100/aL) ∧
    2*(agent12252.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12252, agent12252, scalar12252, tp12252, tm12252, ep12252, em12252, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12252, agent12252, scalar12252, tp12252, tm12252, ep12252, em12252, dsL]

noncomputable def master12252 : MasterCertificate 12252 world12252 agent12252 :=
  master scalar12252 dsL tp12252 tm12252 ep12252 em12252
    (by norm_num [dsL]) (by norm_num [tp12252]) (by norm_num [tm12252])
    (by norm_num [ep12252]) (by norm_num [em12252])
    positive12252 negative12252 tails12252.1 tails12252.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12252.1 guards12252.2

theorem preserves12252 : master12252.toScalarCertificate = scalar12252 := rfl

noncomputable def tp12253 : ℝ := (288014389 / 1250000000)
noncomputable def tm12253 : ℝ := (-((6062138833 / 10000000000)))
noncomputable def ep12253 : ℝ := (50680546778884949 / 100000000000000000000)
noncomputable def em12253 : ℝ := (495975293993927 / 1000000000000000000)
noncomputable def bp12253 : ℝ := (23006736879078241237 / 50000000000000000000)
noncomputable def bm12253 : ℝ := (2339154999364851501 / 5000000000000000000)

theorem positive12253 :
    Eplus aL (agent12253.root+dsL) scalar12253.worldRadius world12253.frame
      agent12253.frame tp12253 ≤ -ep12253 := by
  apply positive_check (eT := (115676871729384864167 / 100000000000000000000)) (y := (37172251791575260693 / 100000000000000000000)) (u := (14502305124715576797 / 10000000000000000000))
  · norm_num [world12253, agent12253, scalar12253, tp12253, tm12253, ep12253, em12253, dsL]
  · norm_num [world12253, agent12253, scalar12253, tp12253, tm12253, ep12253, em12253, dsL]
  · norm_num [world12253, agent12253, scalar12253, tp12253, tm12253, ep12253, em12253, dsL]
  · norm_num [world12253, agent12253, scalar12253, tp12253, tm12253, ep12253, em12253, dsL]
  · norm_num [world12253, agent12253, scalar12253, tp12253, tm12253, ep12253, em12253, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12253, agent12253, tp12253, tm12253, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12253, agent12253, scalar12253, tp12253, tm12253, ep12253, em12253, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12253, agent12253, tp12253, tm12253, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12253, agent12253, scalar12253, tp12253, tm12253, ep12253, em12253, dsL]

theorem negative12253 :
    Eminus aL (agent12253.root+dsL) scalar12253.worldRadius world12253.frame
      agent12253.frame tm12253 ≤ -em12253 := by
  apply negative_check (lo := (68170744451105128737 / 100000000000000000000)) (hi := (34085372225552564369 / 50000000000000000000))
    (y := (-((35425722856658846329 / 50000000000000000000)))) (u := (49237509874970107763 / 100000000000000000000))
  · norm_num [world12253, agent12253, scalar12253, tp12253, tm12253, ep12253, em12253, dsL]
  · norm_num [world12253, agent12253, scalar12253, tp12253, tm12253, ep12253, em12253, dsL]
  · norm_num [world12253, agent12253, scalar12253, tp12253, tm12253, ep12253, em12253, dsL]
  · norm_num [world12253, agent12253, scalar12253, tp12253, tm12253, ep12253, em12253, dsL]
  · norm_num [world12253, agent12253, scalar12253, tp12253, tm12253, ep12253, em12253, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12253, agent12253, tp12253, tm12253, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12253, agent12253, tp12253, tm12253, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12253, agent12253, scalar12253, tp12253, tm12253, ep12253, em12253, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12253, agent12253, tp12253, tm12253, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12253, agent12253, scalar12253, tp12253, tm12253, ep12253, em12253, dsL]

theorem tails12253 :
    exp (-((12253:ℝ)*ep12253)) ≤ scalar12253.upperTail ∧
    exp (-((12253:ℝ)*em12253)) ≤ scalar12253.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12253:ℝ)) (by norm_num [ep12253]) ?_)
      (show bp12253^8 ≤ scalar12253.upperTail by norm_num [bp12253, scalar12253])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12253, bp12253, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12253:ℝ)) (by norm_num [em12253]) ?_)
      (show bm12253^8 ≤ scalar12253.lowerTail by norm_num [bm12253, scalar12253])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12253, bm12253, Finset.sum_range_succ, Nat.factorial]

theorem guards12253 :
    agent12253.root+dsL+scalar12253.worldRadius < √(1/100/aL) ∧
    2*(agent12253.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12253, agent12253, scalar12253, tp12253, tm12253, ep12253, em12253, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12253, agent12253, scalar12253, tp12253, tm12253, ep12253, em12253, dsL]

noncomputable def master12253 : MasterCertificate 12253 world12253 agent12253 :=
  master scalar12253 dsL tp12253 tm12253 ep12253 em12253
    (by norm_num [dsL]) (by norm_num [tp12253]) (by norm_num [tm12253])
    (by norm_num [ep12253]) (by norm_num [em12253])
    positive12253 negative12253 tails12253.1 tails12253.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12253.1 guards12253.2

theorem preserves12253 : master12253.toScalarCertificate = scalar12253 := rfl

noncomputable def tp12254 : ℝ := (2304217787 / 10000000000)
noncomputable def tm12254 : ℝ := (-((757795899 / 1250000000)))
noncomputable def ep12254 : ℝ := (10136732172648727 / 20000000000000000000)
noncomputable def em12254 : ℝ := (49600256009050303 / 100000000000000000000)
noncomputable def bp12254 : ℝ := (46008364214751627247 / 100000000000000000000)
noncomputable def bm12254 : ℝ := (2923640371410378883 / 6250000000000000000)

theorem positive12254 :
    Eplus aL (agent12254.root+dsL) scalar12254.worldRadius world12254.frame
      agent12254.frame tp12254 ≤ -ep12254 := by
  apply positive_check (eT := (23135445080801974897 / 20000000000000000000)) (y := (37173100269911872753 / 100000000000000000000)) (u := (14502428174154892569 / 10000000000000000000))
  · norm_num [world12254, agent12254, scalar12254, tp12254, tm12254, ep12254, em12254, dsL]
  · norm_num [world12254, agent12254, scalar12254, tp12254, tm12254, ep12254, em12254, dsL]
  · norm_num [world12254, agent12254, scalar12254, tp12254, tm12254, ep12254, em12254, dsL]
  · norm_num [world12254, agent12254, scalar12254, tp12254, tm12254, ep12254, em12254, dsL]
  · norm_num [world12254, agent12254, scalar12254, tp12254, tm12254, ep12254, em12254, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12254, agent12254, tp12254, tm12254, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12254, agent12254, scalar12254, tp12254, tm12254, ep12254, em12254, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12254, agent12254, tp12254, tm12254, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12254, agent12254, scalar12254, tp12254, tm12254, ep12254, em12254, dsL]

theorem negative12254 :
    Eminus aL (agent12254.root+dsL) scalar12254.worldRadius world12254.frame
      agent12254.frame tm12254 ≤ -em12254 := by
  apply negative_check (lo := (6817037608954460279 / 10000000000000000000)) (hi := (68170376089544602791 / 100000000000000000000))
    (y := (-((1771288116241110483 / 2500000000000000000)))) (u := (12309367752175945147 / 25000000000000000000))
  · norm_num [world12254, agent12254, scalar12254, tp12254, tm12254, ep12254, em12254, dsL]
  · norm_num [world12254, agent12254, scalar12254, tp12254, tm12254, ep12254, em12254, dsL]
  · norm_num [world12254, agent12254, scalar12254, tp12254, tm12254, ep12254, em12254, dsL]
  · norm_num [world12254, agent12254, scalar12254, tp12254, tm12254, ep12254, em12254, dsL]
  · norm_num [world12254, agent12254, scalar12254, tp12254, tm12254, ep12254, em12254, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12254, agent12254, tp12254, tm12254, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12254, agent12254, tp12254, tm12254, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12254, agent12254, scalar12254, tp12254, tm12254, ep12254, em12254, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12254, agent12254, tp12254, tm12254, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12254, agent12254, scalar12254, tp12254, tm12254, ep12254, em12254, dsL]

theorem tails12254 :
    exp (-((12254:ℝ)*ep12254)) ≤ scalar12254.upperTail ∧
    exp (-((12254:ℝ)*em12254)) ≤ scalar12254.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12254:ℝ)) (by norm_num [ep12254]) ?_)
      (show bp12254^8 ≤ scalar12254.upperTail by norm_num [bp12254, scalar12254])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12254, bp12254, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12254:ℝ)) (by norm_num [em12254]) ?_)
      (show bm12254^8 ≤ scalar12254.lowerTail by norm_num [bm12254, scalar12254])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12254, bm12254, Finset.sum_range_succ, Nat.factorial]

theorem guards12254 :
    agent12254.root+dsL+scalar12254.worldRadius < √(1/100/aL) ∧
    2*(agent12254.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12254, agent12254, scalar12254, tp12254, tm12254, ep12254, em12254, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12254, agent12254, scalar12254, tp12254, tm12254, ep12254, em12254, dsL]

noncomputable def master12254 : MasterCertificate 12254 world12254 agent12254 :=
  master scalar12254 dsL tp12254 tm12254 ep12254 em12254
    (by norm_num [dsL]) (by norm_num [tp12254]) (by norm_num [tm12254])
    (by norm_num [ep12254]) (by norm_num [em12254])
    positive12254 negative12254 tails12254.1 tails12254.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12254.1 guards12254.2

theorem preserves12254 : master12254.toScalarCertificate = scalar12254 := rfl

noncomputable def tp12255 : ℝ := (2304320369 / 10000000000)
noncomputable def tm12255 : ℝ := (-((94728053 / 156250000)))
noncomputable def ep12255 : ℝ := (50686773506187369 / 100000000000000000000)
noncomputable def em12255 : ℝ := (3100186329659777 / 6250000000000000000)
noncomputable def bp12255 : ℝ := (46003255896371391077 / 100000000000000000000)
noncomputable def bm12255 : ℝ := (46773393045739056179 / 100000000000000000000)

theorem positive12255 :
    Eplus aL (agent12255.root+dsL) scalar12255.worldRadius world12255.frame
      agent12255.frame tp12255 ≤ -ep12255 := by
  apply positive_check (eT := (115677578430944071981 / 100000000000000000000)) (y := (7434789517510712443 / 20000000000000000000)) (u := (29005102112615771743 / 20000000000000000000))
  · norm_num [world12255, agent12255, scalar12255, tp12255, tm12255, ep12255, em12255, dsL]
  · norm_num [world12255, agent12255, scalar12255, tp12255, tm12255, ep12255, em12255, dsL]
  · norm_num [world12255, agent12255, scalar12255, tp12255, tm12255, ep12255, em12255, dsL]
  · norm_num [world12255, agent12255, scalar12255, tp12255, tm12255, ep12255, em12255, dsL]
  · norm_num [world12255, agent12255, scalar12255, tp12255, tm12255, ep12255, em12255, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12255, agent12255, tp12255, tm12255, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12255, agent12255, scalar12255, tp12255, tm12255, ep12255, em12255, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12255, agent12255, tp12255, tm12255, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12255, agent12255, scalar12255, tp12255, tm12255, ep12255, em12255, dsL]

theorem negative12255 :
    Eminus aL (agent12255.root+dsL) scalar12255.worldRadius world12255.frame
      agent12255.frame tm12255 ≤ -em12255 := by
  apply negative_check (lo := (68170008358235994369 / 100000000000000000000)) (hi := (6817000835823599437 / 10000000000000000000))
    (y := (-((70851602886114512623 / 100000000000000000000)))) (u := (24618716243529784577 / 50000000000000000000))
  · norm_num [world12255, agent12255, scalar12255, tp12255, tm12255, ep12255, em12255, dsL]
  · norm_num [world12255, agent12255, scalar12255, tp12255, tm12255, ep12255, em12255, dsL]
  · norm_num [world12255, agent12255, scalar12255, tp12255, tm12255, ep12255, em12255, dsL]
  · norm_num [world12255, agent12255, scalar12255, tp12255, tm12255, ep12255, em12255, dsL]
  · norm_num [world12255, agent12255, scalar12255, tp12255, tm12255, ep12255, em12255, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12255, agent12255, tp12255, tm12255, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12255, agent12255, tp12255, tm12255, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12255, agent12255, scalar12255, tp12255, tm12255, ep12255, em12255, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12255, agent12255, tp12255, tm12255, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12255, agent12255, scalar12255, tp12255, tm12255, ep12255, em12255, dsL]

theorem tails12255 :
    exp (-((12255:ℝ)*ep12255)) ≤ scalar12255.upperTail ∧
    exp (-((12255:ℝ)*em12255)) ≤ scalar12255.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12255:ℝ)) (by norm_num [ep12255]) ?_)
      (show bp12255^8 ≤ scalar12255.upperTail by norm_num [bp12255, scalar12255])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12255, bp12255, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12255:ℝ)) (by norm_num [em12255]) ?_)
      (show bm12255^8 ≤ scalar12255.lowerTail by norm_num [bm12255, scalar12255])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12255, bm12255, Finset.sum_range_succ, Nat.factorial]

theorem guards12255 :
    agent12255.root+dsL+scalar12255.worldRadius < √(1/100/aL) ∧
    2*(agent12255.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12255, agent12255, scalar12255, tp12255, tm12255, ep12255, em12255, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12255, agent12255, scalar12255, tp12255, tm12255, ep12255, em12255, dsL]

noncomputable def master12255 : MasterCertificate 12255 world12255 agent12255 :=
  master scalar12255 dsL tp12255 tm12255 ep12255 em12255
    (by norm_num [dsL]) (by norm_num [tp12255]) (by norm_num [tm12255])
    (by norm_num [ep12255]) (by norm_num [em12255])
    positive12255 negative12255 tails12255.1 tails12255.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12255.1 guards12255.2

theorem preserves12255 : master12255.toScalarCertificate = scalar12255 := rfl

noncomputable def tp12256 : ℝ := (230442297 / 1000000000)
noncomputable def tm12256 : ℝ := (-((6062823647 / 10000000000)))
noncomputable def ep12256 : ℝ := (10137976846822517 / 20000000000000000000)
noncomputable def em12256 : ℝ := (1984228190302353 / 4000000000000000000)
noncomputable def bp12256 : ℝ := (22999074568363412259 / 50000000000000000000)
noncomputable def bm12256 : ℝ := (23384270805437886413 / 50000000000000000000)

theorem positive12256 :
    Eplus aL (agent12256.root+dsL) scalar12256.worldRadius world12256.frame
      agent12256.frame tp12256 ≤ -ep12256 := by
  apply positive_check (eT := (115677931629027382843 / 100000000000000000000)) (y := (18587397866960085757 / 50000000000000000000)) (u := (72513370298446796117 / 50000000000000000000))
  · norm_num [world12256, agent12256, scalar12256, tp12256, tm12256, ep12256, em12256, dsL]
  · norm_num [world12256, agent12256, scalar12256, tp12256, tm12256, ep12256, em12256, dsL]
  · norm_num [world12256, agent12256, scalar12256, tp12256, tm12256, ep12256, em12256, dsL]
  · norm_num [world12256, agent12256, scalar12256, tp12256, tm12256, ep12256, em12256, dsL]
  · norm_num [world12256, agent12256, scalar12256, tp12256, tm12256, ep12256, em12256, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12256, agent12256, tp12256, tm12256, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12256, agent12256, scalar12256, tp12256, tm12256, ep12256, em12256, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12256, agent12256, tp12256, tm12256, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12256, agent12256, scalar12256, tp12256, tm12256, ep12256, em12256, dsL]

theorem negative12256 :
    Eminus aL (agent12256.root+dsL) scalar12256.worldRadius world12256.frame
      agent12256.frame tm12256 ≤ -em12256 := by
  apply negative_check (lo := (17042410083792152059 / 25000000000000000000)) (hi := (68169640335168608237 / 100000000000000000000))
    (y := (-((70851682347655653449 / 100000000000000000000)))) (u := (6154674170281555169 / 12500000000000000000))
  · norm_num [world12256, agent12256, scalar12256, tp12256, tm12256, ep12256, em12256, dsL]
  · norm_num [world12256, agent12256, scalar12256, tp12256, tm12256, ep12256, em12256, dsL]
  · norm_num [world12256, agent12256, scalar12256, tp12256, tm12256, ep12256, em12256, dsL]
  · norm_num [world12256, agent12256, scalar12256, tp12256, tm12256, ep12256, em12256, dsL]
  · norm_num [world12256, agent12256, scalar12256, tp12256, tm12256, ep12256, em12256, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12256, agent12256, tp12256, tm12256, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12256, agent12256, tp12256, tm12256, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12256, agent12256, scalar12256, tp12256, tm12256, ep12256, em12256, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12256, agent12256, tp12256, tm12256, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12256, agent12256, scalar12256, tp12256, tm12256, ep12256, em12256, dsL]

theorem tails12256 :
    exp (-((12256:ℝ)*ep12256)) ≤ scalar12256.upperTail ∧
    exp (-((12256:ℝ)*em12256)) ≤ scalar12256.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12256:ℝ)) (by norm_num [ep12256]) ?_)
      (show bp12256^8 ≤ scalar12256.upperTail by norm_num [bp12256, scalar12256])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12256, bp12256, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12256:ℝ)) (by norm_num [em12256]) ?_)
      (show bm12256^8 ≤ scalar12256.lowerTail by norm_num [bm12256, scalar12256])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12256, bm12256, Finset.sum_range_succ, Nat.factorial]

theorem guards12256 :
    agent12256.root+dsL+scalar12256.worldRadius < √(1/100/aL) ∧
    2*(agent12256.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12256, agent12256, scalar12256, tp12256, tm12256, ep12256, em12256, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12256, agent12256, scalar12256, tp12256, tm12256, ep12256, em12256, dsL]

noncomputable def master12256 : MasterCertificate 12256 world12256 agent12256 :=
  master scalar12256 dsL tp12256 tm12256 ep12256 em12256
    (by norm_num [dsL]) (by norm_num [tp12256]) (by norm_num [tm12256])
    (by norm_num [ep12256]) (by norm_num [em12256])
    positive12256 negative12256 tails12256.1 tails12256.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12256.1 guards12256.2

theorem preserves12256 : master12256.toScalarCertificate = scalar12256 := rfl

noncomputable def tp12257 : ℝ := (2304525439 / 10000000000)
noncomputable def tm12257 : ℝ := (-((3031525799 / 5000000000)))
noncomputable def ep12257 : ℝ := (50692994129269731 / 100000000000000000000)
noncomputable def em12257 : ℝ := (4960842747728651 / 10000000000000000000)
noncomputable def bp12257 : ℝ := (11498260793281153147 / 25000000000000000000)
noncomputable def bm12257 : ℝ := (46763690907682928439 / 100000000000000000000)

theorem positive12257 :
    Eplus aL (agent12257.root+dsL) scalar12257.worldRadius world12257.frame
      agent12257.frame tp12257 ≤ -ep12257 := by
  apply positive_check (eT := (7229892743396513631 / 6250000000000000000)) (y := (148702567382282023 / 400000000000000000)) (u := (72513983845116582547 / 50000000000000000000))
  · norm_num [world12257, agent12257, scalar12257, tp12257, tm12257, ep12257, em12257, dsL]
  · norm_num [world12257, agent12257, scalar12257, tp12257, tm12257, ep12257, em12257, dsL]
  · norm_num [world12257, agent12257, scalar12257, tp12257, tm12257, ep12257, em12257, dsL]
  · norm_num [world12257, agent12257, scalar12257, tp12257, tm12257, ep12257, em12257, dsL]
  · norm_num [world12257, agent12257, scalar12257, tp12257, tm12257, ep12257, em12257, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12257, agent12257, tp12257, tm12257, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12257, agent12257, scalar12257, tp12257, tm12257, ep12257, em12257, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12257, agent12257, tp12257, tm12257, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12257, agent12257, scalar12257, tp12257, tm12257, ep12257, em12257, dsL]

theorem negative12257 :
    Eminus aL (agent12257.root+dsL) scalar12257.worldRadius world12257.frame
      agent12257.frame tm12257 ≤ -em12257 := by
  apply negative_check (lo := (13633854713399311899 / 20000000000000000000)) (hi := (8521159195874569937 / 12500000000000000000))
    (y := (-((70851759559933997683 / 100000000000000000000)))) (u := (49237355344953906057 / 100000000000000000000))
  · norm_num [world12257, agent12257, scalar12257, tp12257, tm12257, ep12257, em12257, dsL]
  · norm_num [world12257, agent12257, scalar12257, tp12257, tm12257, ep12257, em12257, dsL]
  · norm_num [world12257, agent12257, scalar12257, tp12257, tm12257, ep12257, em12257, dsL]
  · norm_num [world12257, agent12257, scalar12257, tp12257, tm12257, ep12257, em12257, dsL]
  · norm_num [world12257, agent12257, scalar12257, tp12257, tm12257, ep12257, em12257, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12257, agent12257, tp12257, tm12257, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12257, agent12257, tp12257, tm12257, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12257, agent12257, scalar12257, tp12257, tm12257, ep12257, em12257, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12257, agent12257, tp12257, tm12257, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12257, agent12257, scalar12257, tp12257, tm12257, ep12257, em12257, dsL]

theorem tails12257 :
    exp (-((12257:ℝ)*ep12257)) ≤ scalar12257.upperTail ∧
    exp (-((12257:ℝ)*em12257)) ≤ scalar12257.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12257:ℝ)) (by norm_num [ep12257]) ?_)
      (show bp12257^8 ≤ scalar12257.upperTail by norm_num [bp12257, scalar12257])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12257, bp12257, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12257:ℝ)) (by norm_num [em12257]) ?_)
      (show bm12257^8 ≤ scalar12257.lowerTail by norm_num [bm12257, scalar12257])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12257, bm12257, Finset.sum_range_succ, Nat.factorial]

theorem guards12257 :
    agent12257.root+dsL+scalar12257.worldRadius < √(1/100/aL) ∧
    2*(agent12257.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12257, agent12257, scalar12257, tp12257, tm12257, ep12257, em12257, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12257, agent12257, scalar12257, tp12257, tm12257, ep12257, em12257, dsL]

noncomputable def master12257 : MasterCertificate 12257 world12257 agent12257 :=
  master scalar12257 dsL tp12257 tm12257 ep12257 em12257
    (by norm_num [dsL]) (by norm_num [tp12257]) (by norm_num [tm12257])
    (by norm_num [ep12257]) (by norm_num [em12257])
    positive12257 negative12257 tails12257.1 tails12257.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12257.1 guards12257.2

theorem preserves12257 : master12257.toScalarCertificate = scalar12257 := rfl

noncomputable def tp12258 : ℝ := (92185117 / 400000000)
noncomputable def tm12258 : ℝ := (-((6063279647 / 10000000000)))
noncomputable def ep12258 : ℝ := (25348051291473661 / 50000000000000000000)
noncomputable def em12258 : ℝ := (24805574426466511 / 50000000000000000000)
noncomputable def bp12258 : ℝ := (22993969217248895343 / 50000000000000000000)
noncomputable def bm12258 : ℝ := (4675884135229703921 / 10000000000000000000)

theorem positive12258 :
    Eplus aL (agent12258.root+dsL) scalar12258.worldRadius world12258.frame
      agent12258.frame tp12258 ≤ -ep12258 := by
  apply positive_check (eT := (115678636316208921219 / 100000000000000000000)) (y := (580882635984907397 / 1562500000000000000)) (u := (72514597937801146359 / 50000000000000000000))
  · norm_num [world12258, agent12258, scalar12258, tp12258, tm12258, ep12258, em12258, dsL]
  · norm_num [world12258, agent12258, scalar12258, tp12258, tm12258, ep12258, em12258, dsL]
  · norm_num [world12258, agent12258, scalar12258, tp12258, tm12258, ep12258, em12258, dsL]
  · norm_num [world12258, agent12258, scalar12258, tp12258, tm12258, ep12258, em12258, dsL]
  · norm_num [world12258, agent12258, scalar12258, tp12258, tm12258, ep12258, em12258, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12258, agent12258, tp12258, tm12258, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12258, agent12258, scalar12258, tp12258, tm12258, ep12258, em12258, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12258, agent12258, tp12258, tm12258, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12258, agent12258, scalar12258, tp12258, tm12258, ep12258, em12258, dsL]

theorem negative12258 :
    Eminus aL (agent12258.root+dsL) scalar12258.worldRadius world12258.frame
      agent12258.frame tm12258 ≤ -em12258 := by
  apply negative_check (lo := (3408445316089495869 / 5000000000000000000)) (hi := (68168906321789917381 / 100000000000000000000))
    (y := (-((8856479817016512543 / 12500000000000000000)))) (u := (49237316459177963571 / 100000000000000000000))
  · norm_num [world12258, agent12258, scalar12258, tp12258, tm12258, ep12258, em12258, dsL]
  · norm_num [world12258, agent12258, scalar12258, tp12258, tm12258, ep12258, em12258, dsL]
  · norm_num [world12258, agent12258, scalar12258, tp12258, tm12258, ep12258, em12258, dsL]
  · norm_num [world12258, agent12258, scalar12258, tp12258, tm12258, ep12258, em12258, dsL]
  · norm_num [world12258, agent12258, scalar12258, tp12258, tm12258, ep12258, em12258, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12258, agent12258, tp12258, tm12258, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12258, agent12258, tp12258, tm12258, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12258, agent12258, scalar12258, tp12258, tm12258, ep12258, em12258, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12258, agent12258, tp12258, tm12258, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12258, agent12258, scalar12258, tp12258, tm12258, ep12258, em12258, dsL]

theorem tails12258 :
    exp (-((12258:ℝ)*ep12258)) ≤ scalar12258.upperTail ∧
    exp (-((12258:ℝ)*em12258)) ≤ scalar12258.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12258:ℝ)) (by norm_num [ep12258]) ?_)
      (show bp12258^8 ≤ scalar12258.upperTail by norm_num [bp12258, scalar12258])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12258, bp12258, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12258:ℝ)) (by norm_num [em12258]) ?_)
      (show bm12258^8 ≤ scalar12258.lowerTail by norm_num [bm12258, scalar12258])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12258, bm12258, Finset.sum_range_succ, Nat.factorial]

theorem guards12258 :
    agent12258.root+dsL+scalar12258.worldRadius < √(1/100/aL) ∧
    2*(agent12258.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12258, agent12258, scalar12258, tp12258, tm12258, ep12258, em12258, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12258, agent12258, scalar12258, tp12258, tm12258, ep12258, em12258, dsL]

noncomputable def master12258 : MasterCertificate 12258 world12258 agent12258 :=
  master scalar12258 dsL tp12258 tm12258 ep12258 em12258
    (by norm_num [dsL]) (by norm_num [tp12258]) (by norm_num [tm12258])
    (by norm_num [ep12258]) (by norm_num [em12258])
    positive12258 negative12258 tails12258.1 tails12258.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12258.1 guards12258.2

theorem preserves12258 : master12258.toScalarCertificate = scalar12258 := rfl

noncomputable def tp12259 : ℝ := (1152365183 / 5000000000)
noncomputable def tm12259 : ℝ := (-((3031753733 / 5000000000)))
noncomputable def ep12259 : ℝ := (50699209270540231 / 100000000000000000000)
noncomputable def em12259 : ℝ := (12403467150124221 / 25000000000000000000)
noncomputable def bp12259 : ℝ := (45982835149539186751 / 100000000000000000000)
noncomputable def bm12259 : ℝ := (46753993148172869147 / 100000000000000000000)

theorem positive12259 :
    Eplus aL (agent12259.root+dsL) scalar12259.worldRadius world12259.frame
      agent12259.frame tp12259 ≤ -ep12259 := by
  apply positive_check (eT := (57839494220688991677 / 50000000000000000000)) (y := (7435467025921054127 / 20000000000000000000)) (u := (72515211723223706533 / 50000000000000000000))
  · norm_num [world12259, agent12259, scalar12259, tp12259, tm12259, ep12259, em12259, dsL]
  · norm_num [world12259, agent12259, scalar12259, tp12259, tm12259, ep12259, em12259, dsL]
  · norm_num [world12259, agent12259, scalar12259, tp12259, tm12259, ep12259, em12259, dsL]
  · norm_num [world12259, agent12259, scalar12259, tp12259, tm12259, ep12259, em12259, dsL]
  · norm_num [world12259, agent12259, scalar12259, tp12259, tm12259, ep12259, em12259, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12259, agent12259, tp12259, tm12259, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12259, agent12259, scalar12259, tp12259, tm12259, ep12259, em12259, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12259, agent12259, tp12259, tm12259, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12259, agent12259, scalar12259, tp12259, tm12259, ep12259, em12259, dsL]

theorem negative12259 :
    Eminus aL (agent12259.root+dsL) scalar12259.worldRadius world12259.frame
      agent12259.frame tm12259 ≤ -em12259 := by
  apply negative_check (lo := (68168540012582877907 / 100000000000000000000)) (hi := (17042135003145719477 / 25000000000000000000))
    (y := (-((14170383143619622509 / 20000000000000000000)))) (u := (49237278456863774197 / 100000000000000000000))
  · norm_num [world12259, agent12259, scalar12259, tp12259, tm12259, ep12259, em12259, dsL]
  · norm_num [world12259, agent12259, scalar12259, tp12259, tm12259, ep12259, em12259, dsL]
  · norm_num [world12259, agent12259, scalar12259, tp12259, tm12259, ep12259, em12259, dsL]
  · norm_num [world12259, agent12259, scalar12259, tp12259, tm12259, ep12259, em12259, dsL]
  · norm_num [world12259, agent12259, scalar12259, tp12259, tm12259, ep12259, em12259, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12259, agent12259, tp12259, tm12259, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12259, agent12259, tp12259, tm12259, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12259, agent12259, scalar12259, tp12259, tm12259, ep12259, em12259, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12259, agent12259, tp12259, tm12259, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12259, agent12259, scalar12259, tp12259, tm12259, ep12259, em12259, dsL]

theorem tails12259 :
    exp (-((12259:ℝ)*ep12259)) ≤ scalar12259.upperTail ∧
    exp (-((12259:ℝ)*em12259)) ≤ scalar12259.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12259:ℝ)) (by norm_num [ep12259]) ?_)
      (show bp12259^8 ≤ scalar12259.upperTail by norm_num [bp12259, scalar12259])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12259, bp12259, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12259:ℝ)) (by norm_num [em12259]) ?_)
      (show bm12259^8 ≤ scalar12259.lowerTail by norm_num [bm12259, scalar12259])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12259, bm12259, Finset.sum_range_succ, Nat.factorial]

theorem guards12259 :
    agent12259.root+dsL+scalar12259.worldRadius < √(1/100/aL) ∧
    2*(agent12259.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12259, agent12259, scalar12259, tp12259, tm12259, ep12259, em12259, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12259, agent12259, scalar12259, tp12259, tm12259, ep12259, em12259, dsL]

noncomputable def master12259 : MasterCertificate 12259 world12259 agent12259 :=
  master scalar12259 dsL tp12259 tm12259 ep12259 em12259
    (by norm_num [dsL]) (by norm_num [tp12259]) (by norm_num [tm12259])
    (by norm_num [ep12259]) (by norm_num [em12259])
    positive12259 negative12259 tails12259.1 tails12259.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12259.1 guards12259.2

theorem preserves12259 : master12259.toScalarCertificate = scalar12259 := rfl

noncomputable def tp12260 : ℝ := (2304832729 / 10000000000)
noncomputable def tm12260 : ℝ := (-((6063735213 / 10000000000)))
noncomputable def ep12260 : ℝ := (25351157594418267 / 50000000000000000000)
noncomputable def em12260 : ℝ := (4961658758570977 / 10000000000000000000)
noncomputable def bp12260 : ℝ := (2873608288490593003 / 6250000000000000000)
noncomputable def bm12260 : ℝ := (11687286418760770659 / 25000000000000000000)

theorem positive12260 :
    Eplus aL (agent12260.root+dsL) scalar12260.worldRadius world12260.frame
      agent12260.frame tp12260 ≤ -ep12260 := by
  apply positive_check (eT := (11567934002858910117 / 10000000000000000000)) (y := (37178180757805341147 / 100000000000000000000)) (u := (145031649869792241421 / 100000000000000000000))
  · norm_num [world12260, agent12260, scalar12260, tp12260, tm12260, ep12260, em12260, dsL]
  · norm_num [world12260, agent12260, scalar12260, tp12260, tm12260, ep12260, em12260, dsL]
  · norm_num [world12260, agent12260, scalar12260, tp12260, tm12260, ep12260, em12260, dsL]
  · norm_num [world12260, agent12260, scalar12260, tp12260, tm12260, ep12260, em12260, dsL]
  · norm_num [world12260, agent12260, scalar12260, tp12260, tm12260, ep12260, em12260, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12260, agent12260, tp12260, tm12260, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12260, agent12260, scalar12260, tp12260, tm12260, ep12260, em12260, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12260, agent12260, tp12260, tm12260, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12260, agent12260, scalar12260, tp12260, tm12260, ep12260, em12260, dsL]

theorem negative12260 :
    Eminus aL (agent12260.root+dsL) scalar12260.worldRadius world12260.frame
      agent12260.frame tm12260 ≤ -em12260 := by
  apply negative_check (lo := (68168173958724674633 / 100000000000000000000)) (hi := (34084086979362337317 / 50000000000000000000))
    (y := (-((70851993449288071241 / 100000000000000000000)))) (u := (49237240184156201317 / 100000000000000000000))
  · norm_num [world12260, agent12260, scalar12260, tp12260, tm12260, ep12260, em12260, dsL]
  · norm_num [world12260, agent12260, scalar12260, tp12260, tm12260, ep12260, em12260, dsL]
  · norm_num [world12260, agent12260, scalar12260, tp12260, tm12260, ep12260, em12260, dsL]
  · norm_num [world12260, agent12260, scalar12260, tp12260, tm12260, ep12260, em12260, dsL]
  · norm_num [world12260, agent12260, scalar12260, tp12260, tm12260, ep12260, em12260, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12260, agent12260, tp12260, tm12260, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12260, agent12260, tp12260, tm12260, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12260, agent12260, scalar12260, tp12260, tm12260, ep12260, em12260, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12260, agent12260, tp12260, tm12260, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12260, agent12260, scalar12260, tp12260, tm12260, ep12260, em12260, dsL]

theorem tails12260 :
    exp (-((12260:ℝ)*ep12260)) ≤ scalar12260.upperTail ∧
    exp (-((12260:ℝ)*em12260)) ≤ scalar12260.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12260:ℝ)) (by norm_num [ep12260]) ?_)
      (show bp12260^8 ≤ scalar12260.upperTail by norm_num [bp12260, scalar12260])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12260, bp12260, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12260:ℝ)) (by norm_num [em12260]) ?_)
      (show bm12260^8 ≤ scalar12260.lowerTail by norm_num [bm12260, scalar12260])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12260, bm12260, Finset.sum_range_succ, Nat.factorial]

theorem guards12260 :
    agent12260.root+dsL+scalar12260.worldRadius < √(1/100/aL) ∧
    2*(agent12260.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12260, agent12260, scalar12260, tp12260, tm12260, ep12260, em12260, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12260, agent12260, scalar12260, tp12260, tm12260, ep12260, em12260, dsL]

noncomputable def master12260 : MasterCertificate 12260 world12260 agent12260 :=
  master scalar12260 dsL tp12260 tm12260 ep12260 em12260
    (by norm_num [dsL]) (by norm_num [tp12260]) (by norm_num [tm12260])
    (by norm_num [ep12260]) (by norm_num [em12260])
    positive12260 negative12260 tails12260.1 tails12260.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12260.1 guards12260.2

theorem preserves12260 : master12260.toScalarCertificate = scalar12260 := rfl

noncomputable def tp12261 : ℝ := (460987019 / 2000000000)
noncomputable def tm12261 : ℝ := (-((606396281 / 1000000000)))
noncomputable def ep12261 : ℝ := (12676354631059927 / 25000000000000000000)
noncomputable def em12261 : ℝ := (1240482605266041 / 2500000000000000000)
noncomputable def bp12261 : ℝ := (5746579013909416111 / 12500000000000000000)
noncomputable def bm12261 : ℝ := (46744300077698941319 / 100000000000000000000)

theorem positive12261 :
    Eplus aL (agent12261.root+dsL) scalar12261.worldRadius world12261.frame
      agent12261.frame tp12261 ≤ -ep12261 := by
  apply positive_check (eT := (115679691670004898223 / 100000000000000000000)) (y := (37179026833837462329 / 100000000000000000000)) (u := (566534675597702347 / 390625000000000000))
  · norm_num [world12261, agent12261, scalar12261, tp12261, tm12261, ep12261, em12261, dsL]
  · norm_num [world12261, agent12261, scalar12261, tp12261, tm12261, ep12261, em12261, dsL]
  · norm_num [world12261, agent12261, scalar12261, tp12261, tm12261, ep12261, em12261, dsL]
  · norm_num [world12261, agent12261, scalar12261, tp12261, tm12261, ep12261, em12261, dsL]
  · norm_num [world12261, agent12261, scalar12261, tp12261, tm12261, ep12261, em12261, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12261, agent12261, tp12261, tm12261, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12261, agent12261, scalar12261, tp12261, tm12261, ep12261, em12261, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12261, agent12261, tp12261, tm12261, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12261, agent12261, scalar12261, tp12261, tm12261, ep12261, em12261, dsL]

theorem negative12261 :
    Eminus aL (agent12261.root+dsL) scalar12261.worldRadius world12261.frame
      agent12261.frame tm12261 ≤ -em12261 := by
  apply negative_check (lo := (1704195212404463297 / 2500000000000000000)) (hi := (68167808496178531881 / 100000000000000000000))
    (y := (-((7085207002238939113 / 10000000000000000000)))) (u := (24618601240844411481 / 50000000000000000000))
  · norm_num [world12261, agent12261, scalar12261, tp12261, tm12261, ep12261, em12261, dsL]
  · norm_num [world12261, agent12261, scalar12261, tp12261, tm12261, ep12261, em12261, dsL]
  · norm_num [world12261, agent12261, scalar12261, tp12261, tm12261, ep12261, em12261, dsL]
  · norm_num [world12261, agent12261, scalar12261, tp12261, tm12261, ep12261, em12261, dsL]
  · norm_num [world12261, agent12261, scalar12261, tp12261, tm12261, ep12261, em12261, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12261, agent12261, tp12261, tm12261, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12261, agent12261, tp12261, tm12261, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12261, agent12261, scalar12261, tp12261, tm12261, ep12261, em12261, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12261, agent12261, tp12261, tm12261, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12261, agent12261, scalar12261, tp12261, tm12261, ep12261, em12261, dsL]

theorem tails12261 :
    exp (-((12261:ℝ)*ep12261)) ≤ scalar12261.upperTail ∧
    exp (-((12261:ℝ)*em12261)) ≤ scalar12261.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12261:ℝ)) (by norm_num [ep12261]) ?_)
      (show bp12261^8 ≤ scalar12261.upperTail by norm_num [bp12261, scalar12261])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12261, bp12261, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12261:ℝ)) (by norm_num [em12261]) ?_)
      (show bm12261^8 ≤ scalar12261.lowerTail by norm_num [bm12261, scalar12261])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12261, bm12261, Finset.sum_range_succ, Nat.factorial]

theorem guards12261 :
    agent12261.root+dsL+scalar12261.worldRadius < √(1/100/aL) ∧
    2*(agent12261.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12261, agent12261, scalar12261, tp12261, tm12261, ep12261, em12261, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12261, agent12261, scalar12261, tp12261, tm12261, ep12261, em12261, dsL]

noncomputable def master12261 : MasterCertificate 12261 world12261 agent12261 :=
  master scalar12261 dsL tp12261 tm12261 ep12261 em12261
    (by norm_num [dsL]) (by norm_num [tp12261]) (by norm_num [tm12261])
    (by norm_num [ep12261]) (by norm_num [em12261])
    positive12261 negative12261 tails12261.1 tails12261.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12261.1 guards12261.2

theorem preserves12261 : master12261.toScalarCertificate = scalar12261 := rfl

noncomputable def tp12262 : ℝ := (2305037337 / 10000000000)
noncomputable def tm12262 : ℝ := (-((6064190203 / 10000000000)))
noncomputable def ep12262 : ℝ := (50708520896288343 / 100000000000000000000)
noncomputable def em12262 : ℝ := (49622019933917113 / 100000000000000000000)
noncomputable def bp12262 : ℝ := (459675324946382207 / 1000000000000000000)
noncomputable def bm12262 : ℝ := (46739455311117798061 / 100000000000000000000)

theorem positive12262 :
    Eplus aL (agent12262.root+dsL) scalar12262.worldRadius world12262.frame
      agent12262.frame tp12262 ≤ -ep12262 := by
  apply positive_check (eT := (115680042437242356691 / 100000000000000000000)) (y := (37179871163187100991 / 100000000000000000000)) (u := (453231567229150607 / 312500000000000000))
  · norm_num [world12262, agent12262, scalar12262, tp12262, tm12262, ep12262, em12262, dsL]
  · norm_num [world12262, agent12262, scalar12262, tp12262, tm12262, ep12262, em12262, dsL]
  · norm_num [world12262, agent12262, scalar12262, tp12262, tm12262, ep12262, em12262, dsL]
  · norm_num [world12262, agent12262, scalar12262, tp12262, tm12262, ep12262, em12262, dsL]
  · norm_num [world12262, agent12262, scalar12262, tp12262, tm12262, ep12262, em12262, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12262, agent12262, tp12262, tm12262, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12262, agent12262, scalar12262, tp12262, tm12262, ep12262, em12262, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12262, agent12262, tp12262, tm12262, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12262, agent12262, scalar12262, tp12262, tm12262, ep12262, em12262, dsL]

theorem negative12262 :
    Eminus aL (agent12262.root+dsL) scalar12262.worldRadius world12262.frame
      agent12262.frame tm12262 ≤ -em12262 := by
  apply negative_check (lo := (68167443857528304153 / 100000000000000000000)) (hi := (34083721928764152077 / 50000000000000000000))
    (y := (-((35426072794914601089 / 50000000000000000000)))) (u := (384665353706324463 / 781250000000000000))
  · norm_num [world12262, agent12262, scalar12262, tp12262, tm12262, ep12262, em12262, dsL]
  · norm_num [world12262, agent12262, scalar12262, tp12262, tm12262, ep12262, em12262, dsL]
  · norm_num [world12262, agent12262, scalar12262, tp12262, tm12262, ep12262, em12262, dsL]
  · norm_num [world12262, agent12262, scalar12262, tp12262, tm12262, ep12262, em12262, dsL]
  · norm_num [world12262, agent12262, scalar12262, tp12262, tm12262, ep12262, em12262, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12262, agent12262, tp12262, tm12262, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12262, agent12262, tp12262, tm12262, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12262, agent12262, scalar12262, tp12262, tm12262, ep12262, em12262, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12262, agent12262, tp12262, tm12262, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12262, agent12262, scalar12262, tp12262, tm12262, ep12262, em12262, dsL]

theorem tails12262 :
    exp (-((12262:ℝ)*ep12262)) ≤ scalar12262.upperTail ∧
    exp (-((12262:ℝ)*em12262)) ≤ scalar12262.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12262:ℝ)) (by norm_num [ep12262]) ?_)
      (show bp12262^8 ≤ scalar12262.upperTail by norm_num [bp12262, scalar12262])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12262, bp12262, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12262:ℝ)) (by norm_num [em12262]) ?_)
      (show bm12262^8 ≤ scalar12262.lowerTail by norm_num [bm12262, scalar12262])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12262, bm12262, Finset.sum_range_succ, Nat.factorial]

theorem guards12262 :
    agent12262.root+dsL+scalar12262.worldRadius < √(1/100/aL) ∧
    2*(agent12262.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12262, agent12262, scalar12262, tp12262, tm12262, ep12262, em12262, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12262, agent12262, scalar12262, tp12262, tm12262, ep12262, em12262, dsL]

noncomputable def master12262 : MasterCertificate 12262 world12262 agent12262 :=
  master scalar12262 dsL tp12262 tm12262 ep12262 em12262
    (by norm_num [dsL]) (by norm_num [tp12262]) (by norm_num [tm12262])
    (by norm_num [ep12262]) (by norm_num [em12262])
    positive12262 negative12262 tails12262.1 tails12262.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12262.1 guards12262.2

theorem preserves12262 : master12262.toScalarCertificate = scalar12262 := rfl

noncomputable def tp12263 : ℝ := (576284897 / 2500000000)
noncomputable def tm12263 : ℝ := (-((1212883553 / 2000000000)))
noncomputable def ep12263 : ℝ := (25355810983248191 / 50000000000000000000)
noncomputable def em12263 : ℝ := (49624734459653171 / 100000000000000000000)
noncomputable def bp12263 : ℝ := (1838497360176538539 / 4000000000000000000)
noncomputable def bm12263 : ℝ := (46734611587269084851 / 100000000000000000000)

theorem positive12263 :
    Eplus aL (agent12263.root+dsL) scalar12263.worldRadius world12263.frame
      agent12263.frame tp12263 ≤ -ep12263 := by
  apply positive_check (eT := (23136078660514059009 / 20000000000000000000)) (y := (37180715949193422799 / 100000000000000000000)) (u := (2900706534925949289 / 2000000000000000000))
  · norm_num [world12263, agent12263, scalar12263, tp12263, tm12263, ep12263, em12263, dsL]
  · norm_num [world12263, agent12263, scalar12263, tp12263, tm12263, ep12263, em12263, dsL]
  · norm_num [world12263, agent12263, scalar12263, tp12263, tm12263, ep12263, em12263, dsL]
  · norm_num [world12263, agent12263, scalar12263, tp12263, tm12263, ep12263, em12263, dsL]
  · norm_num [world12263, agent12263, scalar12263, tp12263, tm12263, ep12263, em12263, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12263, agent12263, tp12263, tm12263, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12263, agent12263, scalar12263, tp12263, tm12263, ep12263, em12263, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12263, agent12263, tp12263, tm12263, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12263, agent12263, scalar12263, tp12263, tm12263, ep12263, em12263, dsL]

theorem negative12263 :
    Eminus aL (agent12263.root+dsL) scalar12263.worldRadius world12263.frame
      agent12263.frame tm12263 ≤ -em12263 := by
  apply negative_check (lo := (34083539218003380319 / 50000000000000000000)) (hi := (68167078436006760639 / 100000000000000000000))
    (y := (-((70852223314840218067 / 100000000000000000000)))) (u := (49237127004832270337 / 100000000000000000000))
  · norm_num [world12263, agent12263, scalar12263, tp12263, tm12263, ep12263, em12263, dsL]
  · norm_num [world12263, agent12263, scalar12263, tp12263, tm12263, ep12263, em12263, dsL]
  · norm_num [world12263, agent12263, scalar12263, tp12263, tm12263, ep12263, em12263, dsL]
  · norm_num [world12263, agent12263, scalar12263, tp12263, tm12263, ep12263, em12263, dsL]
  · norm_num [world12263, agent12263, scalar12263, tp12263, tm12263, ep12263, em12263, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12263, agent12263, tp12263, tm12263, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12263, agent12263, tp12263, tm12263, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12263, agent12263, scalar12263, tp12263, tm12263, ep12263, em12263, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12263, agent12263, tp12263, tm12263, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12263, agent12263, scalar12263, tp12263, tm12263, ep12263, em12263, dsL]

theorem tails12263 :
    exp (-((12263:ℝ)*ep12263)) ≤ scalar12263.upperTail ∧
    exp (-((12263:ℝ)*em12263)) ≤ scalar12263.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12263:ℝ)) (by norm_num [ep12263]) ?_)
      (show bp12263^8 ≤ scalar12263.upperTail by norm_num [bp12263, scalar12263])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12263, bp12263, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12263:ℝ)) (by norm_num [em12263]) ?_)
      (show bm12263^8 ≤ scalar12263.lowerTail by norm_num [bm12263, scalar12263])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12263, bm12263, Finset.sum_range_succ, Nat.factorial]

theorem guards12263 :
    agent12263.root+dsL+scalar12263.worldRadius < √(1/100/aL) ∧
    2*(agent12263.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12263, agent12263, scalar12263, tp12263, tm12263, ep12263, em12263, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12263, agent12263, scalar12263, tp12263, tm12263, ep12263, em12263, dsL]

noncomputable def master12263 : MasterCertificate 12263 world12263 agent12263 :=
  master scalar12263 dsL tp12263 tm12263 ep12263 em12263
    (by norm_num [dsL]) (by norm_num [tp12263]) (by norm_num [tm12263])
    (by norm_num [ep12263]) (by norm_num [em12263])
    positive12263 negative12263 tails12263.1 tails12263.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12263.1 guards12263.2

theorem preserves12263 : master12263.toScalarCertificate = scalar12263 := rfl

noncomputable def tp12264 : ℝ := (2305241817 / 10000000000)
noncomputable def tm12264 : ℝ := (-((3032322449 / 5000000000)))
noncomputable def ep12264 : ℝ := (50714721459798369 / 100000000000000000000)
noncomputable def em12264 : ℝ := (2481372374940233 / 5000000000000000000)
noncomputable def bp12264 : ℝ := (11489334208591711349 / 25000000000000000000)
noncomputable def bm12264 : ℝ := (46729769113205053643 / 100000000000000000000)

theorem positive12264 :
    Eplus aL (agent12264.root+dsL) scalar12264.worldRadius world12264.frame
      agent12264.frame tp12264 ≤ -ep12264 := by
  apply positive_check (eT := (57840372019683923883 / 50000000000000000000)) (y := (18590780476993196251 / 50000000000000000000)) (u := (72518276153468992859 / 50000000000000000000))
  · norm_num [world12264, agent12264, scalar12264, tp12264, tm12264, ep12264, em12264, dsL]
  · norm_num [world12264, agent12264, scalar12264, tp12264, tm12264, ep12264, em12264, dsL]
  · norm_num [world12264, agent12264, scalar12264, tp12264, tm12264, ep12264, em12264, dsL]
  · norm_num [world12264, agent12264, scalar12264, tp12264, tm12264, ep12264, em12264, dsL]
  · norm_num [world12264, agent12264, scalar12264, tp12264, tm12264, ep12264, em12264, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12264, agent12264, tp12264, tm12264, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12264, agent12264, scalar12264, tp12264, tm12264, ep12264, em12264, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12264, agent12264, tp12264, tm12264, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12264, agent12264, scalar12264, tp12264, tm12264, ep12264, em12264, dsL]

theorem negative12264 :
    Eminus aL (agent12264.root+dsL) scalar12264.worldRadius world12264.frame
      agent12264.frame tm12264 ≤ -em12264 := by
  apply negative_check (lo := (34083357403745398361 / 50000000000000000000)) (hi := (68166714807490796723 / 100000000000000000000))
    (y := (-((70852298034842608197 / 100000000000000000000)))) (u := (49237090214863540229 / 100000000000000000000))
  · norm_num [world12264, agent12264, scalar12264, tp12264, tm12264, ep12264, em12264, dsL]
  · norm_num [world12264, agent12264, scalar12264, tp12264, tm12264, ep12264, em12264, dsL]
  · norm_num [world12264, agent12264, scalar12264, tp12264, tm12264, ep12264, em12264, dsL]
  · norm_num [world12264, agent12264, scalar12264, tp12264, tm12264, ep12264, em12264, dsL]
  · norm_num [world12264, agent12264, scalar12264, tp12264, tm12264, ep12264, em12264, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12264, agent12264, tp12264, tm12264, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12264, agent12264, tp12264, tm12264, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12264, agent12264, scalar12264, tp12264, tm12264, ep12264, em12264, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12264, agent12264, tp12264, tm12264, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12264, agent12264, scalar12264, tp12264, tm12264, ep12264, em12264, dsL]

theorem tails12264 :
    exp (-((12264:ℝ)*ep12264)) ≤ scalar12264.upperTail ∧
    exp (-((12264:ℝ)*em12264)) ≤ scalar12264.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12264:ℝ)) (by norm_num [ep12264]) ?_)
      (show bp12264^8 ≤ scalar12264.upperTail by norm_num [bp12264, scalar12264])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12264, bp12264, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12264:ℝ)) (by norm_num [em12264]) ?_)
      (show bm12264^8 ≤ scalar12264.lowerTail by norm_num [bm12264, scalar12264])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12264, bm12264, Finset.sum_range_succ, Nat.factorial]

theorem guards12264 :
    agent12264.root+dsL+scalar12264.worldRadius < √(1/100/aL) ∧
    2*(agent12264.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12264, agent12264, scalar12264, tp12264, tm12264, ep12264, em12264, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12264, agent12264, scalar12264, tp12264, tm12264, ep12264, em12264, dsL]

noncomputable def master12264 : MasterCertificate 12264 world12264 agent12264 :=
  master scalar12264 dsL tp12264 tm12264 ep12264 em12264
    (by norm_num [dsL]) (by norm_num [tp12264]) (by norm_num [tm12264])
    (by norm_num [ep12264]) (by norm_num [em12264])
    positive12264 negative12264 tails12264.1 tails12264.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12264.1 guards12264.2

theorem preserves12264 : master12264.toScalarCertificate = scalar12264 := rfl

noncomputable def tp12265 : ℝ := (2305343941 / 10000000000)
noncomputable def tm12265 : ℝ := (-((6064872149 / 10000000000)))
noncomputable def ep12265 : ℝ := (12679454796682227 / 25000000000000000000)
noncomputable def em12265 : ℝ := (49630158909856329 / 100000000000000000000)
noncomputable def bp12265 : ℝ := (45952241117935674259 / 100000000000000000000)
noncomputable def bm12265 : ℝ := (23362463995138186219 / 50000000000000000000)

theorem positive12265 :
    Eplus aL (agent12265.root+dsL) scalar12265.worldRadius world12265.frame
      agent12265.frame tp12265 ≤ -ep12265 := by
  apply positive_check (eT := (115681094040965170451 / 100000000000000000000)) (y := (37182404487219376191 / 100000000000000000000)) (u := (145037775743616708741 / 100000000000000000000))
  · norm_num [world12265, agent12265, scalar12265, tp12265, tm12265, ep12265, em12265, dsL]
  · norm_num [world12265, agent12265, scalar12265, tp12265, tm12265, ep12265, em12265, dsL]
  · norm_num [world12265, agent12265, scalar12265, tp12265, tm12265, ep12265, em12265, dsL]
  · norm_num [world12265, agent12265, scalar12265, tp12265, tm12265, ep12265, em12265, dsL]
  · norm_num [world12265, agent12265, scalar12265, tp12265, tm12265, ep12265, em12265, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12265, agent12265, tp12265, tm12265, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12265, agent12265, scalar12265, tp12265, tm12265, ep12265, em12265, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12265, agent12265, tp12265, tm12265, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12265, agent12265, scalar12265, tp12265, tm12265, ep12265, em12265, dsL]

theorem negative12265 :
    Eminus aL (agent12265.root+dsL) scalar12265.worldRadius world12265.frame
      agent12265.frame tm12265 ≤ -em12265 := by
  apply negative_check (lo := (68166350615768335357 / 100000000000000000000)) (hi := (34083175307884167679 / 50000000000000000000))
    (y := (-((17713093573934627183 / 25000000000000000000)))) (u := (49237052666231744483 / 100000000000000000000))
  · norm_num [world12265, agent12265, scalar12265, tp12265, tm12265, ep12265, em12265, dsL]
  · norm_num [world12265, agent12265, scalar12265, tp12265, tm12265, ep12265, em12265, dsL]
  · norm_num [world12265, agent12265, scalar12265, tp12265, tm12265, ep12265, em12265, dsL]
  · norm_num [world12265, agent12265, scalar12265, tp12265, tm12265, ep12265, em12265, dsL]
  · norm_num [world12265, agent12265, scalar12265, tp12265, tm12265, ep12265, em12265, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12265, agent12265, tp12265, tm12265, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12265, agent12265, tp12265, tm12265, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12265, agent12265, scalar12265, tp12265, tm12265, ep12265, em12265, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12265, agent12265, tp12265, tm12265, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12265, agent12265, scalar12265, tp12265, tm12265, ep12265, em12265, dsL]

theorem tails12265 :
    exp (-((12265:ℝ)*ep12265)) ≤ scalar12265.upperTail ∧
    exp (-((12265:ℝ)*em12265)) ≤ scalar12265.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12265:ℝ)) (by norm_num [ep12265]) ?_)
      (show bp12265^8 ≤ scalar12265.upperTail by norm_num [bp12265, scalar12265])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12265, bp12265, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12265:ℝ)) (by norm_num [em12265]) ?_)
      (show bm12265^8 ≤ scalar12265.lowerTail by norm_num [bm12265, scalar12265])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12265, bm12265, Finset.sum_range_succ, Nat.factorial]

theorem guards12265 :
    agent12265.root+dsL+scalar12265.worldRadius < √(1/100/aL) ∧
    2*(agent12265.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12265, agent12265, scalar12265, tp12265, tm12265, ep12265, em12265, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12265, agent12265, scalar12265, tp12265, tm12265, ep12265, em12265, dsL]

noncomputable def master12265 : MasterCertificate 12265 world12265 agent12265 :=
  master scalar12265 dsL tp12265 tm12265 ep12265 em12265
    (by norm_num [dsL]) (by norm_num [tp12265]) (by norm_num [tm12265])
    (by norm_num [ep12265]) (by norm_num [em12265])
    positive12265 negative12265 tails12265.1 tails12265.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12265.1 guards12265.2

theorem preserves12265 : master12265.toScalarCertificate = scalar12265 := rfl

noncomputable def tp12266 : ℝ := (461089219 / 2000000000)
noncomputable def tm12266 : ℝ := (-((3032549631 / 5000000000)))
noncomputable def ep12266 : ℝ := (5072091562100797 / 10000000000000000000)
noncomputable def em12266 : ℝ := (49632869131352549 / 100000000000000000000)
noncomputable def bp12266 : ℝ := (45947146521337676989 / 100000000000000000000)
noncomputable def bm12266 : ℝ := (4672008790430730183 / 10000000000000000000)

theorem positive12266 :
    Eplus aL (agent12266.root+dsL) scalar12266.worldRadius world12266.frame
      agent12266.frame tp12266 ≤ -ep12266 := by
  apply positive_check (eT := (57840722147064045313 / 50000000000000000000)) (y := (185916244203365121 / 500000000000000000)) (u := (4532468761882981807 / 3125000000000000000))
  · norm_num [world12266, agent12266, scalar12266, tp12266, tm12266, ep12266, em12266, dsL]
  · norm_num [world12266, agent12266, scalar12266, tp12266, tm12266, ep12266, em12266, dsL]
  · norm_num [world12266, agent12266, scalar12266, tp12266, tm12266, ep12266, em12266, dsL]
  · norm_num [world12266, agent12266, scalar12266, tp12266, tm12266, ep12266, em12266, dsL]
  · norm_num [world12266, agent12266, scalar12266, tp12266, tm12266, ep12266, em12266, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12266, agent12266, tp12266, tm12266, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12266, agent12266, scalar12266, tp12266, tm12266, ep12266, em12266, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12266, agent12266, tp12266, tm12266, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12266, agent12266, scalar12266, tp12266, tm12266, ep12266, em12266, dsL]

theorem negative12266 :
    Eminus aL (agent12266.root+dsL) scalar12266.worldRadius world12266.frame
      agent12266.frame tm12266 ≤ -em12266 := by
  apply negative_check (lo := (34082993481784081069 / 50000000000000000000)) (hi := (68165986963568162139 / 100000000000000000000))
    (y := (-((70852449770200549521 / 100000000000000000000)))) (u := (1538656734526410737 / 3125000000000000000))
  · norm_num [world12266, agent12266, scalar12266, tp12266, tm12266, ep12266, em12266, dsL]
  · norm_num [world12266, agent12266, scalar12266, tp12266, tm12266, ep12266, em12266, dsL]
  · norm_num [world12266, agent12266, scalar12266, tp12266, tm12266, ep12266, em12266, dsL]
  · norm_num [world12266, agent12266, scalar12266, tp12266, tm12266, ep12266, em12266, dsL]
  · norm_num [world12266, agent12266, scalar12266, tp12266, tm12266, ep12266, em12266, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12266, agent12266, tp12266, tm12266, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12266, agent12266, tp12266, tm12266, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12266, agent12266, scalar12266, tp12266, tm12266, ep12266, em12266, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12266, agent12266, tp12266, tm12266, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12266, agent12266, scalar12266, tp12266, tm12266, ep12266, em12266, dsL]

theorem tails12266 :
    exp (-((12266:ℝ)*ep12266)) ≤ scalar12266.upperTail ∧
    exp (-((12266:ℝ)*em12266)) ≤ scalar12266.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12266:ℝ)) (by norm_num [ep12266]) ?_)
      (show bp12266^8 ≤ scalar12266.upperTail by norm_num [bp12266, scalar12266])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12266, bp12266, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12266:ℝ)) (by norm_num [em12266]) ?_)
      (show bm12266^8 ≤ scalar12266.lowerTail by norm_num [bm12266, scalar12266])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12266, bm12266, Finset.sum_range_succ, Nat.factorial]

theorem guards12266 :
    agent12266.root+dsL+scalar12266.worldRadius < √(1/100/aL) ∧
    2*(agent12266.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12266, agent12266, scalar12266, tp12266, tm12266, ep12266, em12266, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12266, agent12266, scalar12266, tp12266, tm12266, ep12266, em12266, dsL]

noncomputable def master12266 : MasterCertificate 12266 world12266 agent12266 :=
  master scalar12266 dsL tp12266 tm12266 ep12266 em12266
    (by norm_num [dsL]) (by norm_num [tp12266]) (by norm_num [tm12266])
    (by norm_num [ep12266]) (by norm_num [em12266])
    positive12266 negative12266 tails12266.1 tails12266.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12266.1 guards12266.2

theorem preserves12266 : master12266.toScalarCertificate = scalar12266 := rfl

noncomputable def tp12267 : ℝ := (72048379 / 312500000)
noncomputable def tm12267 : ℝ := (-((758165781 / 1250000000)))
noncomputable def ep12267 : ℝ := (25362005543636479 / 50000000000000000000)
noncomputable def em12267 : ℝ := (387777956620469 / 781250000000000000)
noncomputable def bp12267 : ℝ := (45942052815853023373 / 100000000000000000000)
noncomputable def bm12267 : ℝ := (467152486517622523 / 1000000000000000000)

theorem positive12267 :
    Eplus aL (agent12267.root+dsL) scalar12267.worldRadius world12267.frame
      agent12267.frame tp12267 ≤ -ep12267 := by
  apply positive_check (eT := (115681793695162333107 / 100000000000000000000)) (y := (7436818299787128719 / 20000000000000000000)) (u := (36260055642131392653 / 25000000000000000000))
  · norm_num [world12267, agent12267, scalar12267, tp12267, tm12267, ep12267, em12267, dsL]
  · norm_num [world12267, agent12267, scalar12267, tp12267, tm12267, ep12267, em12267, dsL]
  · norm_num [world12267, agent12267, scalar12267, tp12267, tm12267, ep12267, em12267, dsL]
  · norm_num [world12267, agent12267, scalar12267, tp12267, tm12267, ep12267, em12267, dsL]
  · norm_num [world12267, agent12267, scalar12267, tp12267, tm12267, ep12267, em12267, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12267, agent12267, tp12267, tm12267, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12267, agent12267, scalar12267, tp12267, tm12267, ep12267, em12267, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12267, agent12267, tp12267, tm12267, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12267, agent12267, scalar12267, tp12267, tm12267, ep12267, em12267, dsL]

theorem negative12267 :
    Eminus aL (agent12267.root+dsL) scalar12267.worldRadius world12267.frame
      agent12267.frame tm12267 ≤ -em12267 := by
  apply negative_check (lo := (34082811901725816591 / 50000000000000000000)) (hi := (68165623803451633183 / 100000000000000000000))
    (y := (-((70852524975957588691 / 100000000000000000000)))) (u := (9847395695157762733 / 20000000000000000000))
  · norm_num [world12267, agent12267, scalar12267, tp12267, tm12267, ep12267, em12267, dsL]
  · norm_num [world12267, agent12267, scalar12267, tp12267, tm12267, ep12267, em12267, dsL]
  · norm_num [world12267, agent12267, scalar12267, tp12267, tm12267, ep12267, em12267, dsL]
  · norm_num [world12267, agent12267, scalar12267, tp12267, tm12267, ep12267, em12267, dsL]
  · norm_num [world12267, agent12267, scalar12267, tp12267, tm12267, ep12267, em12267, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12267, agent12267, tp12267, tm12267, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12267, agent12267, tp12267, tm12267, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12267, agent12267, scalar12267, tp12267, tm12267, ep12267, em12267, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12267, agent12267, tp12267, tm12267, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12267, agent12267, scalar12267, tp12267, tm12267, ep12267, em12267, dsL]

theorem tails12267 :
    exp (-((12267:ℝ)*ep12267)) ≤ scalar12267.upperTail ∧
    exp (-((12267:ℝ)*em12267)) ≤ scalar12267.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12267:ℝ)) (by norm_num [ep12267]) ?_)
      (show bp12267^8 ≤ scalar12267.upperTail by norm_num [bp12267, scalar12267])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12267, bp12267, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12267:ℝ)) (by norm_num [em12267]) ?_)
      (show bm12267^8 ≤ scalar12267.lowerTail by norm_num [bm12267, scalar12267])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12267, bm12267, Finset.sum_range_succ, Nat.factorial]

theorem guards12267 :
    agent12267.root+dsL+scalar12267.worldRadius < √(1/100/aL) ∧
    2*(agent12267.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12267, agent12267, scalar12267, tp12267, tm12267, ep12267, em12267, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12267, agent12267, scalar12267, tp12267, tm12267, ep12267, em12267, dsL]

noncomputable def master12267 : MasterCertificate 12267 world12267 agent12267 :=
  master scalar12267 dsL tp12267 tm12267 ep12267 em12267
    (by norm_num [dsL]) (by norm_num [tp12267]) (by norm_num [tm12267])
    (by norm_num [ep12267]) (by norm_num [em12267])
    positive12267 negative12267 tails12267.1 tails12267.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12267.1 guards12267.2

theorem preserves12267 : master12267.toScalarCertificate = scalar12267 := rfl

noncomputable def tp12268 : ℝ := (461130041 / 2000000000)
noncomputable def tm12268 : ℝ := (-((6065553169 / 10000000000)))
noncomputable def ep12268 : ℝ := (50727104511969673 / 100000000000000000000)
noncomputable def em12268 : ℝ := (49638285846299707 / 100000000000000000000)
noncomputable def bp12268 : ℝ := (45936960757735378227 / 100000000000000000000)
noncomputable def bm12268 : ℝ := (23355205478685961257 / 50000000000000000000)

theorem positive12268 :
    Eplus aL (agent12268.root+dsL) scalar12268.worldRadius world12268.frame
      agent12268.frame tp12268 ≤ -ep12268 := by
  apply positive_check (eT := (115682143450098752151 / 100000000000000000000)) (y := (9296233891828680541 / 25000000000000000000)) (u := (7252072340617396847 / 5000000000000000000))
  · norm_num [world12268, agent12268, scalar12268, tp12268, tm12268, ep12268, em12268, dsL]
  · norm_num [world12268, agent12268, scalar12268, tp12268, tm12268, ep12268, em12268, dsL]
  · norm_num [world12268, agent12268, scalar12268, tp12268, tm12268, ep12268, em12268, dsL]
  · norm_num [world12268, agent12268, scalar12268, tp12268, tm12268, ep12268, em12268, dsL]
  · norm_num [world12268, agent12268, scalar12268, tp12268, tm12268, ep12268, em12268, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12268, agent12268, tp12268, tm12268, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12268, agent12268, scalar12268, tp12268, tm12268, ep12268, em12268, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12268, agent12268, tp12268, tm12268, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12268, agent12268, scalar12268, tp12268, tm12268, ep12268, em12268, dsL]

theorem negative12268 :
    Eminus aL (agent12268.root+dsL) scalar12268.worldRadius world12268.frame
      agent12268.frame tm12268 ≤ -em12268 := by
  apply negative_check (lo := (68165260868378481039 / 100000000000000000000)) (hi := (852065760854731013 / 1250000000000000000))
    (y := (-((70852600538322605227 / 100000000000000000000)))) (u := (2461847063558873551 / 5000000000000000000))
  · norm_num [world12268, agent12268, scalar12268, tp12268, tm12268, ep12268, em12268, dsL]
  · norm_num [world12268, agent12268, scalar12268, tp12268, tm12268, ep12268, em12268, dsL]
  · norm_num [world12268, agent12268, scalar12268, tp12268, tm12268, ep12268, em12268, dsL]
  · norm_num [world12268, agent12268, scalar12268, tp12268, tm12268, ep12268, em12268, dsL]
  · norm_num [world12268, agent12268, scalar12268, tp12268, tm12268, ep12268, em12268, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12268, agent12268, tp12268, tm12268, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12268, agent12268, tp12268, tm12268, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12268, agent12268, scalar12268, tp12268, tm12268, ep12268, em12268, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12268, agent12268, tp12268, tm12268, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12268, agent12268, scalar12268, tp12268, tm12268, ep12268, em12268, dsL]

theorem tails12268 :
    exp (-((12268:ℝ)*ep12268)) ≤ scalar12268.upperTail ∧
    exp (-((12268:ℝ)*em12268)) ≤ scalar12268.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12268:ℝ)) (by norm_num [ep12268]) ?_)
      (show bp12268^8 ≤ scalar12268.upperTail by norm_num [bp12268, scalar12268])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12268, bp12268, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12268:ℝ)) (by norm_num [em12268]) ?_)
      (show bm12268^8 ≤ scalar12268.lowerTail by norm_num [bm12268, scalar12268])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12268, bm12268, Finset.sum_range_succ, Nat.factorial]

theorem guards12268 :
    agent12268.root+dsL+scalar12268.worldRadius < √(1/100/aL) ∧
    2*(agent12268.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12268, agent12268, scalar12268, tp12268, tm12268, ep12268, em12268, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12268, agent12268, scalar12268, tp12268, tm12268, ep12268, em12268, dsL]

noncomputable def master12268 : MasterCertificate 12268 world12268 agent12268 :=
  master scalar12268 dsL tp12268 tm12268 ep12268 em12268
    (by norm_num [dsL]) (by norm_num [tp12268]) (by norm_num [tm12268])
    (by norm_num [ep12268]) (by norm_num [em12268])
    positive12268 negative12268 tails12268.1 tails12268.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12268.1 guards12268.2

theorem preserves12268 : master12268.toScalarCertificate = scalar12268 := rfl

noncomputable def tp12269 : ℝ := (2305752187 / 10000000000)
noncomputable def tm12269 : ℝ := (-((6065779747 / 10000000000)))
noncomputable def ep12269 : ℝ := (12682549280610993 / 25000000000000000000)
noncomputable def em12269 : ℝ := (49640992492186009 / 100000000000000000000)
noncomputable def bp12269 : ℝ := (2296593474117178967 / 5000000000000000000)
noncomputable def bm12269 : ℝ := (46705573987192901597 / 100000000000000000000)

theorem positive12269 :
    Eplus aL (agent12269.root+dsL) scalar12269.worldRadius world12269.frame
      agent12269.frame tp12269 ≤ -ep12269 := by
  apply positive_check (eT := (28920623135747218989 / 25000000000000000000)) (y := (37185778140199708973 / 100000000000000000000)) (u := (29008533779479848351 / 20000000000000000000))
  · norm_num [world12269, agent12269, scalar12269, tp12269, tm12269, ep12269, em12269, dsL]
  · norm_num [world12269, agent12269, scalar12269, tp12269, tm12269, ep12269, em12269, dsL]
  · norm_num [world12269, agent12269, scalar12269, tp12269, tm12269, ep12269, em12269, dsL]
  · norm_num [world12269, agent12269, scalar12269, tp12269, tm12269, ep12269, em12269, dsL]
  · norm_num [world12269, agent12269, scalar12269, tp12269, tm12269, ep12269, em12269, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12269, agent12269, tp12269, tm12269, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12269, agent12269, scalar12269, tp12269, tm12269, ep12269, em12269, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12269, agent12269, tp12269, tm12269, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12269, agent12269, scalar12269, tp12269, tm12269, ep12269, em12269, dsL]

theorem negative12269 :
    Eminus aL (agent12269.root+dsL) scalar12269.worldRadius world12269.frame
      agent12269.frame tm12269 ≤ -em12269 := by
  apply negative_check (lo := (68164899355578784999 / 100000000000000000000)) (hi := (13632979871115757 / 20000000000000000))
    (y := (-((35426336533202124829 / 50000000000000000000)))) (u := (49236905560581456747 / 100000000000000000000))
  · norm_num [world12269, agent12269, scalar12269, tp12269, tm12269, ep12269, em12269, dsL]
  · norm_num [world12269, agent12269, scalar12269, tp12269, tm12269, ep12269, em12269, dsL]
  · norm_num [world12269, agent12269, scalar12269, tp12269, tm12269, ep12269, em12269, dsL]
  · norm_num [world12269, agent12269, scalar12269, tp12269, tm12269, ep12269, em12269, dsL]
  · norm_num [world12269, agent12269, scalar12269, tp12269, tm12269, ep12269, em12269, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12269, agent12269, tp12269, tm12269, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12269, agent12269, tp12269, tm12269, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12269, agent12269, scalar12269, tp12269, tm12269, ep12269, em12269, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12269, agent12269, tp12269, tm12269, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12269, agent12269, scalar12269, tp12269, tm12269, ep12269, em12269, dsL]

theorem tails12269 :
    exp (-((12269:ℝ)*ep12269)) ≤ scalar12269.upperTail ∧
    exp (-((12269:ℝ)*em12269)) ≤ scalar12269.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12269:ℝ)) (by norm_num [ep12269]) ?_)
      (show bp12269^8 ≤ scalar12269.upperTail by norm_num [bp12269, scalar12269])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12269, bp12269, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12269:ℝ)) (by norm_num [em12269]) ?_)
      (show bm12269^8 ≤ scalar12269.lowerTail by norm_num [bm12269, scalar12269])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12269, bm12269, Finset.sum_range_succ, Nat.factorial]

theorem guards12269 :
    agent12269.root+dsL+scalar12269.worldRadius < √(1/100/aL) ∧
    2*(agent12269.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12269, agent12269, scalar12269, tp12269, tm12269, ep12269, em12269, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12269, agent12269, scalar12269, tp12269, tm12269, ep12269, em12269, dsL]

noncomputable def master12269 : MasterCertificate 12269 world12269 agent12269 :=
  master scalar12269 dsL tp12269 tm12269 ep12269 em12269
    (by norm_num [dsL]) (by norm_num [tp12269]) (by norm_num [tm12269])
    (by norm_num [ep12269]) (by norm_num [em12269])
    positive12269 negative12269 tails12269.1 tails12269.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12269.1 guards12269.2

theorem preserves12269 : master12269.toScalarCertificate = scalar12269 := rfl

noncomputable def tp12270 : ℝ := (2305854103 / 10000000000)
noncomputable def tm12270 : ℝ := (-((606600639 / 1000000000)))
noncomputable def ep12270 : ℝ := (50733287817168559 / 100000000000000000000)
noncomputable def em12270 : ℝ := (24821848680794541 / 50000000000000000000)
noncomputable def bp12270 : ℝ := (2870423735350044491 / 6250000000000000000)
noncomputable def bm12270 : ℝ := (46700738474333540981 / 100000000000000000000)

theorem positive12270 :
    Eplus aL (agent12270.root+dsL) scalar12270.worldRadius world12270.frame
      agent12270.frame tp12270 ≤ -ep12270 := by
  apply positive_check (eT := (115682841185811715479 / 100000000000000000000)) (y := (3718662016763471651 / 10000000000000000000)) (u := (72521945100802838013 / 50000000000000000000))
  · norm_num [world12270, agent12270, scalar12270, tp12270, tm12270, ep12270, em12270, dsL]
  · norm_num [world12270, agent12270, scalar12270, tp12270, tm12270, ep12270, em12270, dsL]
  · norm_num [world12270, agent12270, scalar12270, tp12270, tm12270, ep12270, em12270, dsL]
  · norm_num [world12270, agent12270, scalar12270, tp12270, tm12270, ep12270, em12270, dsL]
  · norm_num [world12270, agent12270, scalar12270, tp12270, tm12270, ep12270, em12270, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12270, agent12270, tp12270, tm12270, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12270, agent12270, scalar12270, tp12270, tm12270, ep12270, em12270, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12270, agent12270, tp12270, tm12270, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12270, agent12270, scalar12270, tp12270, tm12270, ep12270, em12270, dsL]

theorem negative12270 :
    Eminus aL (agent12270.root+dsL) scalar12270.worldRadius world12270.frame
      agent12270.frame tm12270 ≤ -em12270 := by
  apply negative_check (lo := (8520567188483638689 / 12500000000000000000)) (hi := (68164537507869109513 / 100000000000000000000))
    (y := (-((70852747320526262483 / 100000000000000000000)))) (u := (6154608625020387533 / 12500000000000000000))
  · norm_num [world12270, agent12270, scalar12270, tp12270, tm12270, ep12270, em12270, dsL]
  · norm_num [world12270, agent12270, scalar12270, tp12270, tm12270, ep12270, em12270, dsL]
  · norm_num [world12270, agent12270, scalar12270, tp12270, tm12270, ep12270, em12270, dsL]
  · norm_num [world12270, agent12270, scalar12270, tp12270, tm12270, ep12270, em12270, dsL]
  · norm_num [world12270, agent12270, scalar12270, tp12270, tm12270, ep12270, em12270, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12270, agent12270, tp12270, tm12270, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12270, agent12270, tp12270, tm12270, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12270, agent12270, scalar12270, tp12270, tm12270, ep12270, em12270, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12270, agent12270, tp12270, tm12270, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12270, agent12270, scalar12270, tp12270, tm12270, ep12270, em12270, dsL]

theorem tails12270 :
    exp (-((12270:ℝ)*ep12270)) ≤ scalar12270.upperTail ∧
    exp (-((12270:ℝ)*em12270)) ≤ scalar12270.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12270:ℝ)) (by norm_num [ep12270]) ?_)
      (show bp12270^8 ≤ scalar12270.upperTail by norm_num [bp12270, scalar12270])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12270, bp12270, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12270:ℝ)) (by norm_num [em12270]) ?_)
      (show bm12270^8 ≤ scalar12270.lowerTail by norm_num [bm12270, scalar12270])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12270, bm12270, Finset.sum_range_succ, Nat.factorial]

theorem guards12270 :
    agent12270.root+dsL+scalar12270.worldRadius < √(1/100/aL) ∧
    2*(agent12270.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12270, agent12270, scalar12270, tp12270, tm12270, ep12270, em12270, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12270, agent12270, scalar12270, tp12270, tm12270, ep12270, em12270, dsL]

noncomputable def master12270 : MasterCertificate 12270 world12270 agent12270 :=
  master scalar12270 dsL tp12270 tm12270 ep12270 em12270
    (by norm_num [dsL]) (by norm_num [tp12270]) (by norm_num [tm12270])
    (by norm_num [ep12270]) (by norm_num [em12270])
    positive12270 negative12270 tails12270.1 tails12270.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12270.1 guards12270.2

theorem preserves12270 : master12270.toScalarCertificate = scalar12270 := rfl

noncomputable def tp12271 : ℝ := (2305955999 / 10000000000)
noncomputable def tm12271 : ℝ := (-((1213246599 / 2000000000)))
noncomputable def ep12271 : ℝ := (50736377223745569 / 100000000000000000000)
noncomputable def em12271 : ℝ := (4964640104549897 / 10000000000000000000)
noncomputable def bp12271 : ℝ := (367373529322978761 / 800000000000000000)
noncomputable def bm12271 : ℝ := (5836987999431918583 / 12500000000000000000)

theorem positive12271 :
    Eplus aL (agent12271.root+dsL) scalar12271.worldRadius world12271.frame
      agent12271.frame tp12271 ≤ -ep12271 := by
  apply positive_check (eT := (57841594857400929641 / 50000000000000000000)) (y := (7437492429611669707 / 20000000000000000000)) (u := (29009022289581633611 / 20000000000000000000))
  · norm_num [world12271, agent12271, scalar12271, tp12271, tm12271, ep12271, em12271, dsL]
  · norm_num [world12271, agent12271, scalar12271, tp12271, tm12271, ep12271, em12271, dsL]
  · norm_num [world12271, agent12271, scalar12271, tp12271, tm12271, ep12271, em12271, dsL]
  · norm_num [world12271, agent12271, scalar12271, tp12271, tm12271, ep12271, em12271, dsL]
  · norm_num [world12271, agent12271, scalar12271, tp12271, tm12271, ep12271, em12271, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12271, agent12271, tp12271, tm12271, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12271, agent12271, scalar12271, tp12271, tm12271, ep12271, em12271, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12271, agent12271, tp12271, tm12271, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12271, agent12271, scalar12271, tp12271, tm12271, ep12271, em12271, dsL]

theorem negative12271 :
    Eminus aL (agent12271.root+dsL) scalar12271.worldRadius world12271.frame
      agent12271.frame tm12271 ≤ -em12271 := by
  apply negative_check (lo := (34082087884414218713 / 50000000000000000000)) (hi := (68164175768828437427 / 100000000000000000000))
    (y := (-((70852821745558776099 / 100000000000000000000)))) (u := (12309208088905243641 / 25000000000000000000))
  · norm_num [world12271, agent12271, scalar12271, tp12271, tm12271, ep12271, em12271, dsL]
  · norm_num [world12271, agent12271, scalar12271, tp12271, tm12271, ep12271, em12271, dsL]
  · norm_num [world12271, agent12271, scalar12271, tp12271, tm12271, ep12271, em12271, dsL]
  · norm_num [world12271, agent12271, scalar12271, tp12271, tm12271, ep12271, em12271, dsL]
  · norm_num [world12271, agent12271, scalar12271, tp12271, tm12271, ep12271, em12271, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12271, agent12271, tp12271, tm12271, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12271, agent12271, tp12271, tm12271, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12271, agent12271, scalar12271, tp12271, tm12271, ep12271, em12271, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12271, agent12271, tp12271, tm12271, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12271, agent12271, scalar12271, tp12271, tm12271, ep12271, em12271, dsL]

theorem tails12271 :
    exp (-((12271:ℝ)*ep12271)) ≤ scalar12271.upperTail ∧
    exp (-((12271:ℝ)*em12271)) ≤ scalar12271.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12271:ℝ)) (by norm_num [ep12271]) ?_)
      (show bp12271^8 ≤ scalar12271.upperTail by norm_num [bp12271, scalar12271])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12271, bp12271, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12271:ℝ)) (by norm_num [em12271]) ?_)
      (show bm12271^8 ≤ scalar12271.lowerTail by norm_num [bm12271, scalar12271])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12271, bm12271, Finset.sum_range_succ, Nat.factorial]

theorem guards12271 :
    agent12271.root+dsL+scalar12271.worldRadius < √(1/100/aL) ∧
    2*(agent12271.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12271, agent12271, scalar12271, tp12271, tm12271, ep12271, em12271, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12271, agent12271, scalar12271, tp12271, tm12271, ep12271, em12271, dsL]

noncomputable def master12271 : MasterCertificate 12271 world12271 agent12271 :=
  master scalar12271 dsL tp12271 tm12271 ep12271 em12271
    (by norm_num [dsL]) (by norm_num [tp12271]) (by norm_num [tm12271])
    (by norm_num [ep12271]) (by norm_num [em12271])
    positive12271 negative12271 tails12271.1 tails12271.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12271.1 guards12271.2

theorem preserves12271 : master12271.toScalarCertificate = scalar12271 := rfl

noncomputable def tp12272 : ℝ := (2306057791 / 10000000000)
noncomputable def tm12272 : ℝ := (-((6066459413 / 10000000000)))
noncomputable def ep12272 : ℝ := (6342433108540167 / 12500000000000000000)
noncomputable def em12272 : ℝ := (24824551552658739 / 50000000000000000000)
noncomputable def bp12272 : ℝ := (183666416061592127 / 400000000000000000)
noncomputable def bm12272 : ℝ := (46691070864690445617 / 100000000000000000000)

theorem positive12272 :
    Eplus aL (agent12272.root+dsL) scalar12272.worldRadius world12272.frame
      agent12272.frame tp12272 ≤ -ep12272 := by
  apply positive_check (eT := (185093660025622003 / 160000000000000000)) (y := (37188302673558268093 / 100000000000000000000)) (u := (29009266118835976987 / 20000000000000000000))
  · norm_num [world12272, agent12272, scalar12272, tp12272, tm12272, ep12272, em12272, dsL]
  · norm_num [world12272, agent12272, scalar12272, tp12272, tm12272, ep12272, em12272, dsL]
  · norm_num [world12272, agent12272, scalar12272, tp12272, tm12272, ep12272, em12272, dsL]
  · norm_num [world12272, agent12272, scalar12272, tp12272, tm12272, ep12272, em12272, dsL]
  · norm_num [world12272, agent12272, scalar12272, tp12272, tm12272, ep12272, em12272, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12272, agent12272, tp12272, tm12272, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12272, agent12272, scalar12272, tp12272, tm12272, ep12272, em12272, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12272, agent12272, tp12272, tm12272, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12272, agent12272, scalar12272, tp12272, tm12272, ep12272, em12272, dsL]

theorem negative12272 :
    Eminus aL (agent12272.root+dsL) scalar12272.worldRadius world12272.frame
      agent12272.frame tm12272 ≤ -em12272 := by
  apply negative_check (lo := (68163814780158795979 / 100000000000000000000)) (hi := (3408190739007939799 / 5000000000000000000))
    (y := (-((14170578957197417313 / 20000000000000000000)))) (u := (24618398196420434599 / 50000000000000000000))
  · norm_num [world12272, agent12272, scalar12272, tp12272, tm12272, ep12272, em12272, dsL]
  · norm_num [world12272, agent12272, scalar12272, tp12272, tm12272, ep12272, em12272, dsL]
  · norm_num [world12272, agent12272, scalar12272, tp12272, tm12272, ep12272, em12272, dsL]
  · norm_num [world12272, agent12272, scalar12272, tp12272, tm12272, ep12272, em12272, dsL]
  · norm_num [world12272, agent12272, scalar12272, tp12272, tm12272, ep12272, em12272, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12272, agent12272, tp12272, tm12272, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12272, agent12272, tp12272, tm12272, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12272, agent12272, scalar12272, tp12272, tm12272, ep12272, em12272, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12272, agent12272, tp12272, tm12272, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12272, agent12272, scalar12272, tp12272, tm12272, ep12272, em12272, dsL]

theorem tails12272 :
    exp (-((12272:ℝ)*ep12272)) ≤ scalar12272.upperTail ∧
    exp (-((12272:ℝ)*em12272)) ≤ scalar12272.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12272:ℝ)) (by norm_num [ep12272]) ?_)
      (show bp12272^8 ≤ scalar12272.upperTail by norm_num [bp12272, scalar12272])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12272, bp12272, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12272:ℝ)) (by norm_num [em12272]) ?_)
      (show bm12272^8 ≤ scalar12272.lowerTail by norm_num [bm12272, scalar12272])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12272, bm12272, Finset.sum_range_succ, Nat.factorial]

theorem guards12272 :
    agent12272.root+dsL+scalar12272.worldRadius < √(1/100/aL) ∧
    2*(agent12272.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12272, agent12272, scalar12272, tp12272, tm12272, ep12272, em12272, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12272, agent12272, scalar12272, tp12272, tm12272, ep12272, em12272, dsL]

noncomputable def master12272 : MasterCertificate 12272 world12272 agent12272 :=
  master scalar12272 dsL tp12272 tm12272 ep12272 em12272
    (by norm_num [dsL]) (by norm_num [tp12272]) (by norm_num [tm12272])
    (by norm_num [ep12272]) (by norm_num [em12272])
    positive12272 negative12272 tails12272.1 tails12272.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12272.1 guards12272.2

theorem preserves12272 : master12272.toScalarCertificate = scalar12272 := rfl

noncomputable def tp12273 : ℝ := (2306159701 / 10000000000)
noncomputable def tm12273 : ℝ := (-((6066686077 / 10000000000)))
noncomputable def ep12273 : ℝ := (50742553738467513 / 100000000000000000000)
noncomputable def em12273 : ℝ := (1551618956695439 / 3125000000000000000)
noncomputable def bp12273 : ℝ := (11477879052839413763 / 25000000000000000000)
noncomputable def bm12273 : ℝ := (46686236880897962571 / 100000000000000000000)

theorem positive12273 :
    Eplus aL (agent12273.root+dsL) scalar12273.worldRadius world12273.frame
      agent12273.frame tp12273 ≤ -ep12273 := by
  apply positive_check (eT := (57841943105973536109 / 50000000000000000000)) (y := (3718914284651466679 / 10000000000000000000)) (u := (18130943654917892783 / 12500000000000000000))
  · norm_num [world12273, agent12273, scalar12273, tp12273, tm12273, ep12273, em12273, dsL]
  · norm_num [world12273, agent12273, scalar12273, tp12273, tm12273, ep12273, em12273, dsL]
  · norm_num [world12273, agent12273, scalar12273, tp12273, tm12273, ep12273, em12273, dsL]
  · norm_num [world12273, agent12273, scalar12273, tp12273, tm12273, ep12273, em12273, dsL]
  · norm_num [world12273, agent12273, scalar12273, tp12273, tm12273, ep12273, em12273, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12273, agent12273, tp12273, tm12273, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12273, agent12273, scalar12273, tp12273, tm12273, ep12273, em12273, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12273, agent12273, tp12273, tm12273, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12273, agent12273, scalar12273, tp12273, tm12273, ep12273, em12273, dsL]

theorem negative12273 :
    Eminus aL (agent12273.root+dsL) scalar12273.worldRadius world12273.frame
      agent12273.frame tm12273 ≤ -em12273 := by
  apply negative_check (lo := (13632690535438022113 / 20000000000000000000)) (hi := (34081726338595055283 / 50000000000000000000))
    (y := (-((35426482790362610649 / 50000000000000000000)))) (u := (24618380767896067717 / 50000000000000000000))
  · norm_num [world12273, agent12273, scalar12273, tp12273, tm12273, ep12273, em12273, dsL]
  · norm_num [world12273, agent12273, scalar12273, tp12273, tm12273, ep12273, em12273, dsL]
  · norm_num [world12273, agent12273, scalar12273, tp12273, tm12273, ep12273, em12273, dsL]
  · norm_num [world12273, agent12273, scalar12273, tp12273, tm12273, ep12273, em12273, dsL]
  · norm_num [world12273, agent12273, scalar12273, tp12273, tm12273, ep12273, em12273, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12273, agent12273, tp12273, tm12273, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12273, agent12273, tp12273, tm12273, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12273, agent12273, scalar12273, tp12273, tm12273, ep12273, em12273, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12273, agent12273, tp12273, tm12273, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12273, agent12273, scalar12273, tp12273, tm12273, ep12273, em12273, dsL]

theorem tails12273 :
    exp (-((12273:ℝ)*ep12273)) ≤ scalar12273.upperTail ∧
    exp (-((12273:ℝ)*em12273)) ≤ scalar12273.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12273:ℝ)) (by norm_num [ep12273]) ?_)
      (show bp12273^8 ≤ scalar12273.upperTail by norm_num [bp12273, scalar12273])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12273, bp12273, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12273:ℝ)) (by norm_num [em12273]) ?_)
      (show bm12273^8 ≤ scalar12273.lowerTail by norm_num [bm12273, scalar12273])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12273, bm12273, Finset.sum_range_succ, Nat.factorial]

theorem guards12273 :
    agent12273.root+dsL+scalar12273.worldRadius < √(1/100/aL) ∧
    2*(agent12273.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12273, agent12273, scalar12273, tp12273, tm12273, ep12273, em12273, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12273, agent12273, scalar12273, tp12273, tm12273, ep12273, em12273, dsL]

noncomputable def master12273 : MasterCertificate 12273 world12273 agent12273 :=
  master scalar12273 dsL tp12273 tm12273 ep12273 em12273
    (by norm_num [dsL]) (by norm_num [tp12273]) (by norm_num [tm12273])
    (by norm_num [ep12273]) (by norm_num [em12273])
    positive12273 negative12273 tails12273.1 tails12273.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12273.1 guards12273.2

theorem preserves12273 : master12273.toScalarCertificate = scalar12273 := rfl

noncomputable def tp12274 : ℝ := (2306261769 / 10000000000)
noncomputable def tm12274 : ℝ := (-((3033456599 / 5000000000)))
noncomputable def ep12274 : ℝ := (50745644150999123 / 100000000000000000000)
noncomputable def em12274 : ℝ := (49654512188039899 / 100000000000000000000)
noncomputable def bp12274 : ℝ := (45906427530243603277 / 100000000000000000000)
noncomputable def bm12274 : ℝ := (11670350400800068157 / 25000000000000000000)

theorem positive12274 :
    Eplus aL (agent12274.root+dsL) scalar12274.worldRadius world12274.frame
      agent12274.frame tp12274 ≤ -ep12274 := by
  apply positive_check (eT := (23136847218971490539 / 20000000000000000000)) (y := (18594990376553166523 / 50000000000000000000)) (u := (29009752921482217309 / 20000000000000000000))
  · norm_num [world12274, agent12274, scalar12274, tp12274, tm12274, ep12274, em12274, dsL]
  · norm_num [world12274, agent12274, scalar12274, tp12274, tm12274, ep12274, em12274, dsL]
  · norm_num [world12274, agent12274, scalar12274, tp12274, tm12274, ep12274, em12274, dsL]
  · norm_num [world12274, agent12274, scalar12274, tp12274, tm12274, ep12274, em12274, dsL]
  · norm_num [world12274, agent12274, scalar12274, tp12274, tm12274, ep12274, em12274, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12274, agent12274, tp12274, tm12274, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12274, agent12274, scalar12274, tp12274, tm12274, ep12274, em12274, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12274, agent12274, tp12274, tm12274, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12274, agent12274, scalar12274, tp12274, tm12274, ep12274, em12274, dsL]

theorem negative12274 :
    Eminus aL (agent12274.root+dsL) scalar12274.worldRadius world12274.frame
      agent12274.frame tm12274 ≤ -em12274 := by
  apply negative_check (lo := (68163088551460124731 / 100000000000000000000)) (hi := (17040772137865031183 / 25000000000000000000))
    (y := (-((70853030092836202763 / 100000000000000000000)))) (u := (49236729772128135491 / 100000000000000000000))
  · norm_num [world12274, agent12274, scalar12274, tp12274, tm12274, ep12274, em12274, dsL]
  · norm_num [world12274, agent12274, scalar12274, tp12274, tm12274, ep12274, em12274, dsL]
  · norm_num [world12274, agent12274, scalar12274, tp12274, tm12274, ep12274, em12274, dsL]
  · norm_num [world12274, agent12274, scalar12274, tp12274, tm12274, ep12274, em12274, dsL]
  · norm_num [world12274, agent12274, scalar12274, tp12274, tm12274, ep12274, em12274, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12274, agent12274, tp12274, tm12274, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12274, agent12274, tp12274, tm12274, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12274, agent12274, scalar12274, tp12274, tm12274, ep12274, em12274, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12274, agent12274, tp12274, tm12274, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12274, agent12274, scalar12274, tp12274, tm12274, ep12274, em12274, dsL]

theorem tails12274 :
    exp (-((12274:ℝ)*ep12274)) ≤ scalar12274.upperTail ∧
    exp (-((12274:ℝ)*em12274)) ≤ scalar12274.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12274:ℝ)) (by norm_num [ep12274]) ?_)
      (show bp12274^8 ≤ scalar12274.upperTail by norm_num [bp12274, scalar12274])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12274, bp12274, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12274:ℝ)) (by norm_num [em12274]) ?_)
      (show bm12274^8 ≤ scalar12274.lowerTail by norm_num [bm12274, scalar12274])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12274, bm12274, Finset.sum_range_succ, Nat.factorial]

theorem guards12274 :
    agent12274.root+dsL+scalar12274.worldRadius < √(1/100/aL) ∧
    2*(agent12274.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12274, agent12274, scalar12274, tp12274, tm12274, ep12274, em12274, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12274, agent12274, scalar12274, tp12274, tm12274, ep12274, em12274, dsL]

noncomputable def master12274 : MasterCertificate 12274 world12274 agent12274 :=
  master scalar12274 dsL tp12274 tm12274 ep12274 em12274
    (by norm_num [dsL]) (by norm_num [tp12274]) (by norm_num [tm12274])
    (by norm_num [ep12274]) (by norm_num [em12274])
    positive12274 negative12274 tails12274.1 tails12274.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12274.1 guards12274.2

theorem preserves12274 : master12274.toScalarCertificate = scalar12274 := rfl

end BstLean.Part261
