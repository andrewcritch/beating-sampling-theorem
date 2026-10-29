import BstLean.Part261Checker
import BstLean.Part268Scalar16
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12750 : ℝ := (72533947 / 312500000)
noncomputable def tm12750 : ℝ := (-((6073084137 / 10000000000)))
noncomputable def ep12750 : ℝ := (51561511814941909 / 100000000000000000000)
noncomputable def em12750 : ℝ := (10045722099016747 / 20000000000000000000)
noncomputable def bp12750 : ℝ := (43965647547953027559 / 100000000000000000000)
noncomputable def bm12750 : ℝ := (22454802826273715619 / 50000000000000000000)

theorem positive12750 :
    Eplus aL (agent12750.root+dsL) scalar12750.worldRadius world12750.frame
      agent12750.frame tp12750 ≤ -ep12750 := by
  apply positive_check (eT := (57805061916365641109 / 50000000000000000000)) (y := (4737121430258197843 / 12500000000000000000)) (u := (146077879454141363807 / 100000000000000000000))
  · norm_num [world12750, agent12750, scalar12750, tp12750, tm12750, ep12750, em12750, dsL]
  · norm_num [world12750, agent12750, scalar12750, tp12750, tm12750, ep12750, em12750, dsL]
  · norm_num [world12750, agent12750, scalar12750, tp12750, tm12750, ep12750, em12750, dsL]
  · norm_num [world12750, agent12750, scalar12750, tp12750, tm12750, ep12750, em12750, dsL]
  · norm_num [world12750, agent12750, scalar12750, tp12750, tm12750, ep12750, em12750, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12750, agent12750, tp12750, tm12750, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12750, agent12750, scalar12750, tp12750, tm12750, ep12750, em12750, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12750, agent12750, tp12750, tm12750, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12750, agent12750, scalar12750, tp12750, tm12750, ep12750, em12750, dsL]

theorem negative12750 :
    Eminus aL (agent12750.root+dsL) scalar12750.worldRadius world12750.frame
      agent12750.frame tm12750 ≤ -em12750 := by
  apply negative_check (lo := (6841831146932966183 / 10000000000000000000)) (hi := (68418311469329661831 / 100000000000000000000))
    (y := (-((35840620831560060801 / 50000000000000000000)))) (u := (762978585709718843 / 1562500000000000000))
  · norm_num [world12750, agent12750, scalar12750, tp12750, tm12750, ep12750, em12750, dsL]
  · norm_num [world12750, agent12750, scalar12750, tp12750, tm12750, ep12750, em12750, dsL]
  · norm_num [world12750, agent12750, scalar12750, tp12750, tm12750, ep12750, em12750, dsL]
  · norm_num [world12750, agent12750, scalar12750, tp12750, tm12750, ep12750, em12750, dsL]
  · norm_num [world12750, agent12750, scalar12750, tp12750, tm12750, ep12750, em12750, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12750, agent12750, tp12750, tm12750, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12750, agent12750, tp12750, tm12750, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12750, agent12750, scalar12750, tp12750, tm12750, ep12750, em12750, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12750, agent12750, tp12750, tm12750, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12750, agent12750, scalar12750, tp12750, tm12750, ep12750, em12750, dsL]

theorem tails12750 :
    exp (-((12750:ℝ)*ep12750)) ≤ scalar12750.upperTail ∧
    exp (-((12750:ℝ)*em12750)) ≤ scalar12750.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12750:ℝ)) (by norm_num [ep12750]) ?_)
      (show bp12750^8 ≤ scalar12750.upperTail by norm_num [bp12750, scalar12750])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12750, bp12750, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12750:ℝ)) (by norm_num [em12750]) ?_)
      (show bm12750^8 ≤ scalar12750.lowerTail by norm_num [bm12750, scalar12750])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12750, bm12750, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12750 :
    agent12750.root+dsL+scalar12750.worldRadius < √(1/100/aL) ∧
    2*(agent12750.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12750, agent12750, scalar12750, tp12750, tm12750, ep12750, em12750, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12750, agent12750, scalar12750, tp12750, tm12750, ep12750, em12750, dsL]

noncomputable def master12750 : MasterCertificate 12750 world12750 agent12750 :=
  master scalar12750 dsL tp12750 tm12750 ep12750 em12750
    (by norm_num [dsL]) (by norm_num [tp12750]) (by norm_num [tm12750])
    (by norm_num [ep12750]) (by norm_num [em12750])
    positive12750 negative12750 tails12750.1 tails12750.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12750.1 tailGuards12750.2

theorem preserves12750 : master12750.toScalarCertificate = scalar12750 := rfl

noncomputable def tp12751 : ℝ := (2321169823 / 10000000000)
noncomputable def tm12751 : ℝ := (-((6073263239 / 10000000000)))
noncomputable def ep12751 : ℝ := (10312814604054601 / 20000000000000000000)
noncomputable def em12751 : ℝ := (6278850567998691 / 12500000000000000000)
noncomputable def bp12751 : ℝ := (2198050966937444299 / 5000000000000000000)
noncomputable def bm12751 : ℝ := (44905215676523607097 / 100000000000000000000)

theorem positive12751 :
    Eplus aL (agent12751.root+dsL) scalar12751.worldRadius world12751.frame
      agent12751.frame tp12751 ≤ -ep12751 := by
  apply positive_check (eT := (115610358755182248733 / 100000000000000000000)) (y := (3789774582456166309 / 10000000000000000000)) (u := (2921580213201008533 / 2000000000000000000))
  · norm_num [world12751, agent12751, scalar12751, tp12751, tm12751, ep12751, em12751, dsL]
  · norm_num [world12751, agent12751, scalar12751, tp12751, tm12751, ep12751, em12751, dsL]
  · norm_num [world12751, agent12751, scalar12751, tp12751, tm12751, ep12751, em12751, dsL]
  · norm_num [world12751, agent12751, scalar12751, tp12751, tm12751, ep12751, em12751, dsL]
  · norm_num [world12751, agent12751, scalar12751, tp12751, tm12751, ep12751, em12751, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12751, agent12751, tp12751, tm12751, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12751, agent12751, scalar12751, tp12751, tm12751, ep12751, em12751, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12751, agent12751, tp12751, tm12751, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12751, agent12751, scalar12751, tp12751, tm12751, ep12751, em12751, dsL]

theorem negative12751 :
    Eminus aL (agent12751.root+dsL) scalar12751.worldRadius world12751.frame
      agent12751.frame tm12751 ≤ -em12751 := by
  apply negative_check (lo := (68418116269052839869 / 100000000000000000000)) (hi := (6841811626905283987 / 10000000000000000000))
    (y := (-((71681294186887464891 / 100000000000000000000)))) (u := (4883060383774251833 / 10000000000000000000))
  · norm_num [world12751, agent12751, scalar12751, tp12751, tm12751, ep12751, em12751, dsL]
  · norm_num [world12751, agent12751, scalar12751, tp12751, tm12751, ep12751, em12751, dsL]
  · norm_num [world12751, agent12751, scalar12751, tp12751, tm12751, ep12751, em12751, dsL]
  · norm_num [world12751, agent12751, scalar12751, tp12751, tm12751, ep12751, em12751, dsL]
  · norm_num [world12751, agent12751, scalar12751, tp12751, tm12751, ep12751, em12751, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12751, agent12751, tp12751, tm12751, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12751, agent12751, tp12751, tm12751, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12751, agent12751, scalar12751, tp12751, tm12751, ep12751, em12751, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12751, agent12751, tp12751, tm12751, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12751, agent12751, scalar12751, tp12751, tm12751, ep12751, em12751, dsL]

theorem tails12751 :
    exp (-((12751:ℝ)*ep12751)) ≤ scalar12751.upperTail ∧
    exp (-((12751:ℝ)*em12751)) ≤ scalar12751.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12751:ℝ)) (by norm_num [ep12751]) ?_)
      (show bp12751^8 ≤ scalar12751.upperTail by norm_num [bp12751, scalar12751])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12751, bp12751, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12751:ℝ)) (by norm_num [em12751]) ?_)
      (show bm12751^8 ≤ scalar12751.lowerTail by norm_num [bm12751, scalar12751])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12751, bm12751, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12751 :
    agent12751.root+dsL+scalar12751.worldRadius < √(1/100/aL) ∧
    2*(agent12751.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12751, agent12751, scalar12751, tp12751, tm12751, ep12751, em12751, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12751, agent12751, scalar12751, tp12751, tm12751, ep12751, em12751, dsL]

noncomputable def master12751 : MasterCertificate 12751 world12751 agent12751 :=
  master scalar12751 dsL tp12751 tm12751 ep12751 em12751
    (by norm_num [dsL]) (by norm_num [tp12751]) (by norm_num [tm12751])
    (by norm_num [ep12751]) (by norm_num [em12751])
    positive12751 negative12751 tails12751.1 tails12751.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12751.1 tailGuards12751.2

theorem preserves12751 : master12751.toScalarCertificate = scalar12751 := rfl

noncomputable def tp12752 : ℝ := (464250671 / 2000000000)
noncomputable def tm12752 : ℝ := (-((6073442157 / 10000000000)))
noncomputable def ep12752 : ℝ := (25783316185823931 / 50000000000000000000)
noncomputable def em12752 : ℝ := (10046599384857301 / 20000000000000000000)
noncomputable def bp12752 : ℝ := (43956392634299269317 / 100000000000000000000)
noncomputable def bm12752 : ℝ := (44900827077594810099 / 100000000000000000000)

theorem positive12752 :
    Eplus aL (agent12752.root+dsL) scalar12752.worldRadius world12752.frame
      agent12752.frame tp12752 ≤ -ep12752 := by
  apply positive_check (eT := (11561059380433742697 / 10000000000000000000)) (y := (18949260320177219201 / 50000000000000000000)) (u := (146080142507679812081 / 100000000000000000000))
  · norm_num [world12752, agent12752, scalar12752, tp12752, tm12752, ep12752, em12752, dsL]
  · norm_num [world12752, agent12752, scalar12752, tp12752, tm12752, ep12752, em12752, dsL]
  · norm_num [world12752, agent12752, scalar12752, tp12752, tm12752, ep12752, em12752, dsL]
  · norm_num [world12752, agent12752, scalar12752, tp12752, tm12752, ep12752, em12752, dsL]
  · norm_num [world12752, agent12752, scalar12752, tp12752, tm12752, ep12752, em12752, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12752, agent12752, tp12752, tm12752, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12752, agent12752, scalar12752, tp12752, tm12752, ep12752, em12752, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12752, agent12752, tp12752, tm12752, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12752, agent12752, scalar12752, tp12752, tm12752, ep12752, em12752, dsL]

theorem negative12752 :
    Eminus aL (agent12752.root+dsL) scalar12752.worldRadius world12752.frame
      agent12752.frame tm12752 ≤ -em12752 := by
  apply negative_check (lo := (4276120112412141161 / 6250000000000000000)) (hi := (68417921798594258577 / 100000000000000000000))
    (y := (-((8960168131464199983 / 12500000000000000000)))) (u := (9766115800029418481 / 20000000000000000000))
  · norm_num [world12752, agent12752, scalar12752, tp12752, tm12752, ep12752, em12752, dsL]
  · norm_num [world12752, agent12752, scalar12752, tp12752, tm12752, ep12752, em12752, dsL]
  · norm_num [world12752, agent12752, scalar12752, tp12752, tm12752, ep12752, em12752, dsL]
  · norm_num [world12752, agent12752, scalar12752, tp12752, tm12752, ep12752, em12752, dsL]
  · norm_num [world12752, agent12752, scalar12752, tp12752, tm12752, ep12752, em12752, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12752, agent12752, tp12752, tm12752, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12752, agent12752, tp12752, tm12752, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12752, agent12752, scalar12752, tp12752, tm12752, ep12752, em12752, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12752, agent12752, tp12752, tm12752, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12752, agent12752, scalar12752, tp12752, tm12752, ep12752, em12752, dsL]

theorem tails12752 :
    exp (-((12752:ℝ)*ep12752)) ≤ scalar12752.upperTail ∧
    exp (-((12752:ℝ)*em12752)) ≤ scalar12752.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12752:ℝ)) (by norm_num [ep12752]) ?_)
      (show bp12752^8 ≤ scalar12752.upperTail by norm_num [bp12752, scalar12752])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12752, bp12752, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12752:ℝ)) (by norm_num [em12752]) ?_)
      (show bm12752^8 ≤ scalar12752.lowerTail by norm_num [bm12752, scalar12752])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12752, bm12752, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12752 :
    agent12752.root+dsL+scalar12752.worldRadius < √(1/100/aL) ∧
    2*(agent12752.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12752, agent12752, scalar12752, tp12752, tm12752, ep12752, em12752, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12752, agent12752, scalar12752, tp12752, tm12752, ep12752, em12752, dsL]

noncomputable def master12752 : MasterCertificate 12752 world12752 agent12752 :=
  master scalar12752 dsL tp12752 tm12752 ep12752 em12752
    (by norm_num [dsL]) (by norm_num [tp12752]) (by norm_num [tm12752])
    (by norm_num [ep12752]) (by norm_num [em12752])
    positive12752 negative12752 tails12752.1 tails12752.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12752.1 tailGuards12752.2

theorem preserves12752 : master12752.toScalarCertificate = scalar12752 := rfl

noncomputable def tp12753 : ℝ := (1160668423 / 5000000000)
noncomputable def tm12753 : ℝ := (-((6073620977 / 10000000000)))
noncomputable def ep12753 : ℝ := (51569191163748369 / 100000000000000000000)
noncomputable def em12753 : ℝ := (25117594380682371 / 50000000000000000000)
noncomputable def bp12753 : ℝ := (21975883263711678309 / 50000000000000000000)
noncomputable def bm12753 : ℝ := (44896439050274370953 / 100000000000000000000)

theorem positive12753 :
    Eplus aL (agent12753.root+dsL) scalar12753.worldRadius world12753.frame
      agent12753.frame tp12753 ≤ -ep12753 := by
  apply positive_check (eT := (115610828590076053007 / 100000000000000000000)) (y := (236870595321177137 / 625000000000000000)) (u := (73040637032482298343 / 50000000000000000000))
  · norm_num [world12753, agent12753, scalar12753, tp12753, tm12753, ep12753, em12753, dsL]
  · norm_num [world12753, agent12753, scalar12753, tp12753, tm12753, ep12753, em12753, dsL]
  · norm_num [world12753, agent12753, scalar12753, tp12753, tm12753, ep12753, em12753, dsL]
  · norm_num [world12753, agent12753, scalar12753, tp12753, tm12753, ep12753, em12753, dsL]
  · norm_num [world12753, agent12753, scalar12753, tp12753, tm12753, ep12753, em12753, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12753, agent12753, tp12753, tm12753, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12753, agent12753, scalar12753, tp12753, tm12753, ep12753, em12753, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12753, agent12753, tp12753, tm12753, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12753, agent12753, scalar12753, tp12753, tm12753, ep12753, em12753, dsL]

theorem negative12753 :
    Eminus aL (agent12753.root+dsL) scalar12753.worldRadius world12753.frame
      agent12753.frame tm12753 ≤ -em12753 := by
  apply negative_check (lo := (34208863845101815429 / 50000000000000000000)) (hi := (68417727690203630859 / 100000000000000000000))
    (y := (-((7168139634066972359 / 10000000000000000000)))) (u := (24415276977729638319 / 50000000000000000000))
  · norm_num [world12753, agent12753, scalar12753, tp12753, tm12753, ep12753, em12753, dsL]
  · norm_num [world12753, agent12753, scalar12753, tp12753, tm12753, ep12753, em12753, dsL]
  · norm_num [world12753, agent12753, scalar12753, tp12753, tm12753, ep12753, em12753, dsL]
  · norm_num [world12753, agent12753, scalar12753, tp12753, tm12753, ep12753, em12753, dsL]
  · norm_num [world12753, agent12753, scalar12753, tp12753, tm12753, ep12753, em12753, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12753, agent12753, tp12753, tm12753, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12753, agent12753, tp12753, tm12753, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12753, agent12753, scalar12753, tp12753, tm12753, ep12753, em12753, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12753, agent12753, tp12753, tm12753, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12753, agent12753, scalar12753, tp12753, tm12753, ep12753, em12753, dsL]

theorem tails12753 :
    exp (-((12753:ℝ)*ep12753)) ≤ scalar12753.upperTail ∧
    exp (-((12753:ℝ)*em12753)) ≤ scalar12753.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12753:ℝ)) (by norm_num [ep12753]) ?_)
      (show bp12753^8 ≤ scalar12753.upperTail by norm_num [bp12753, scalar12753])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12753, bp12753, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12753:ℝ)) (by norm_num [em12753]) ?_)
      (show bm12753^8 ≤ scalar12753.lowerTail by norm_num [bm12753, scalar12753])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12753, bm12753, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12753 :
    agent12753.root+dsL+scalar12753.worldRadius < √(1/100/aL) ∧
    2*(agent12753.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12753, agent12753, scalar12753, tp12753, tm12753, ep12753, em12753, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12753, agent12753, scalar12753, tp12753, tm12753, ep12753, em12753, dsL]

noncomputable def master12753 : MasterCertificate 12753 world12753 agent12753 :=
  master scalar12753 dsL tp12753 tm12753 ep12753 em12753
    (by norm_num [dsL]) (by norm_num [tp12753]) (by norm_num [tm12753])
    (by norm_num [ep12753]) (by norm_num [em12753])
    positive12753 negative12753 tails12753.1 tails12753.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12753.1 tailGuards12753.2

theorem preserves12753 : master12753.toScalarCertificate = scalar12753 := rfl

noncomputable def tp12754 : ℝ := (580355063 / 2500000000)
noncomputable def tm12754 : ℝ := (-((3036899789 / 5000000000)))
noncomputable def ep12754 : ℝ := (1031434971522819 / 2000000000000000000)
noncomputable def em12754 : ℝ := (25118689653428471 / 50000000000000000000)
noncomputable def bp12754 : ℝ := (10986785398236325041 / 25000000000000000000)
noncomputable def bm12754 : ℝ := (22446026065085061341 / 50000000000000000000)

theorem positive12754 :
    Eplus aL (agent12754.root+dsL) scalar12754.worldRadius world12754.frame
      agent12754.frame tp12754 ≤ -ep12754 := by
  apply positive_check (eT := (115611062794551789603 / 100000000000000000000)) (y := (37900068730256866761 / 100000000000000000000)) (u := (146082403977120171291 / 100000000000000000000))
  · norm_num [world12754, agent12754, scalar12754, tp12754, tm12754, ep12754, em12754, dsL]
  · norm_num [world12754, agent12754, scalar12754, tp12754, tm12754, ep12754, em12754, dsL]
  · norm_num [world12754, agent12754, scalar12754, tp12754, tm12754, ep12754, em12754, dsL]
  · norm_num [world12754, agent12754, scalar12754, tp12754, tm12754, ep12754, em12754, dsL]
  · norm_num [world12754, agent12754, scalar12754, tp12754, tm12754, ep12754, em12754, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12754, agent12754, tp12754, tm12754, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12754, agent12754, scalar12754, tp12754, tm12754, ep12754, em12754, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12754, agent12754, tp12754, tm12754, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12754, agent12754, scalar12754, tp12754, tm12754, ep12754, em12754, dsL]

theorem negative12754 :
    Eminus aL (agent12754.root+dsL) scalar12754.worldRadius world12754.frame
      agent12754.frame tm12754 ≤ -em12754 := by
  apply negative_check (lo := (34208767230576231439 / 50000000000000000000)) (hi := (68417534461152462879 / 100000000000000000000))
    (y := (-((7168144592409640753 / 10000000000000000000)))) (u := (24415264871801679653 / 50000000000000000000))
  · norm_num [world12754, agent12754, scalar12754, tp12754, tm12754, ep12754, em12754, dsL]
  · norm_num [world12754, agent12754, scalar12754, tp12754, tm12754, ep12754, em12754, dsL]
  · norm_num [world12754, agent12754, scalar12754, tp12754, tm12754, ep12754, em12754, dsL]
  · norm_num [world12754, agent12754, scalar12754, tp12754, tm12754, ep12754, em12754, dsL]
  · norm_num [world12754, agent12754, scalar12754, tp12754, tm12754, ep12754, em12754, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12754, agent12754, tp12754, tm12754, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12754, agent12754, tp12754, tm12754, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12754, agent12754, scalar12754, tp12754, tm12754, ep12754, em12754, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12754, agent12754, tp12754, tm12754, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12754, agent12754, scalar12754, tp12754, tm12754, ep12754, em12754, dsL]

theorem tails12754 :
    exp (-((12754:ℝ)*ep12754)) ≤ scalar12754.upperTail ∧
    exp (-((12754:ℝ)*em12754)) ≤ scalar12754.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12754:ℝ)) (by norm_num [ep12754]) ?_)
      (show bp12754^8 ≤ scalar12754.upperTail by norm_num [bp12754, scalar12754])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12754, bp12754, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12754:ℝ)) (by norm_num [em12754]) ?_)
      (show bm12754^8 ≤ scalar12754.lowerTail by norm_num [bm12754, scalar12754])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12754, bm12754, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12754 :
    agent12754.root+dsL+scalar12754.worldRadius < √(1/100/aL) ∧
    2*(agent12754.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12754, agent12754, scalar12754, tp12754, tm12754, ep12754, em12754, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12754, agent12754, scalar12754, tp12754, tm12754, ep12754, em12754, dsL]

noncomputable def master12754 : MasterCertificate 12754 world12754 agent12754 :=
  master scalar12754 dsL tp12754 tm12754 ep12754 em12754
    (by norm_num [dsL]) (by norm_num [tp12754]) (by norm_num [tm12754])
    (by norm_num [ep12754]) (by norm_num [em12754])
    positive12754 negative12754 tails12754.1 tails12754.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12754.1 tailGuards12754.2

theorem preserves12754 : master12754.toScalarCertificate = scalar12754 := rfl

noncomputable def tp12755 : ℝ := (2321503719 / 10000000000)
noncomputable def tm12755 : ℝ := (-((189811821 / 312500000)))
noncomputable def ep12755 : ℝ := (25787152230185337 / 50000000000000000000)
noncomputable def em12755 : ℝ := (25119784234411693 / 50000000000000000000)
noncomputable def bp12755 : ℝ := (43942517934833594041 / 100000000000000000000)
noncomputable def bm12755 : ℝ := (8977533276611583583 / 20000000000000000000)

theorem positive12755 :
    Eplus aL (agent12755.root+dsL) scalar12755.worldRadius world12755.frame
      agent12755.frame tp12755 ≤ -ep12755 := by
  apply positive_check (eT := (115611297472485640121 / 100000000000000000000)) (y := (59220068103983433 / 156250000000000000)) (u := (14608353591020508933 / 10000000000000000000))
  · norm_num [world12755, agent12755, scalar12755, tp12755, tm12755, ep12755, em12755, dsL]
  · norm_num [world12755, agent12755, scalar12755, tp12755, tm12755, ep12755, em12755, dsL]
  · norm_num [world12755, agent12755, scalar12755, tp12755, tm12755, ep12755, em12755, dsL]
  · norm_num [world12755, agent12755, scalar12755, tp12755, tm12755, ep12755, em12755, dsL]
  · norm_num [world12755, agent12755, scalar12755, tp12755, tm12755, ep12755, em12755, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12755, agent12755, tp12755, tm12755, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12755, agent12755, scalar12755, tp12755, tm12755, ep12755, em12755, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12755, agent12755, tp12755, tm12755, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12755, agent12755, scalar12755, tp12755, tm12755, ep12755, em12755, dsL]

theorem negative12755 :
    Eminus aL (agent12755.root+dsL) scalar12755.worldRadius world12755.frame
      agent12755.frame tm12755 ≤ -em12755 := by
  apply negative_check (lo := (3420867038879443401 / 5000000000000000000)) (hi := (68417340777588868021 / 100000000000000000000))
    (y := (-((35840748475432850061 / 50000000000000000000)))) (u := (12207626206741989941 / 25000000000000000000))
  · norm_num [world12755, agent12755, scalar12755, tp12755, tm12755, ep12755, em12755, dsL]
  · norm_num [world12755, agent12755, scalar12755, tp12755, tm12755, ep12755, em12755, dsL]
  · norm_num [world12755, agent12755, scalar12755, tp12755, tm12755, ep12755, em12755, dsL]
  · norm_num [world12755, agent12755, scalar12755, tp12755, tm12755, ep12755, em12755, dsL]
  · norm_num [world12755, agent12755, scalar12755, tp12755, tm12755, ep12755, em12755, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12755, agent12755, tp12755, tm12755, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12755, agent12755, tp12755, tm12755, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12755, agent12755, scalar12755, tp12755, tm12755, ep12755, em12755, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12755, agent12755, tp12755, tm12755, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12755, agent12755, scalar12755, tp12755, tm12755, ep12755, em12755, dsL]

theorem tails12755 :
    exp (-((12755:ℝ)*ep12755)) ≤ scalar12755.upperTail ∧
    exp (-((12755:ℝ)*em12755)) ≤ scalar12755.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12755:ℝ)) (by norm_num [ep12755]) ?_)
      (show bp12755^8 ≤ scalar12755.upperTail by norm_num [bp12755, scalar12755])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12755, bp12755, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12755:ℝ)) (by norm_num [em12755]) ?_)
      (show bm12755^8 ≤ scalar12755.lowerTail by norm_num [bm12755, scalar12755])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12755, bm12755, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12755 :
    agent12755.root+dsL+scalar12755.worldRadius < √(1/100/aL) ∧
    2*(agent12755.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12755, agent12755, scalar12755, tp12755, tm12755, ep12755, em12755, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12755, agent12755, scalar12755, tp12755, tm12755, ep12755, em12755, dsL]

noncomputable def master12755 : MasterCertificate 12755 world12755 agent12755 :=
  master scalar12755 dsL tp12755 tm12755 ep12755 em12755
    (by norm_num [dsL]) (by norm_num [tp12755]) (by norm_num [tm12755])
    (by norm_num [ep12755]) (by norm_num [em12755])
    positive12755 negative12755 tails12755.1 tails12755.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12755.1 tailGuards12755.2

theorem preserves12755 : master12755.toScalarCertificate = scalar12755 := rfl

noncomputable def tp12756 : ℝ := (2321587079 / 10000000000)
noncomputable def tm12756 : ℝ := (-((1214831369 / 2000000000)))
noncomputable def ep12756 : ℝ := (51576859300047053 / 100000000000000000000)
noncomputable def em12756 : ℝ := (25120878316111603 / 50000000000000000000)
noncomputable def bp12756 : ℝ := (43937895214227704283 / 100000000000000000000)
noncomputable def bm12756 : ℝ := (44883281533409217497 / 100000000000000000000)

theorem positive12756 :
    Eplus aL (agent12756.root+dsL) scalar12756.worldRadius world12756.frame
      agent12756.frame tp12756 ≤ -ep12756 := by
  apply positive_check (eT := (57805765705122635803 / 50000000000000000000)) (y := (9475404256821823491 / 25000000000000000000)) (u := (18260583223019078261 / 12500000000000000000))
  · norm_num [world12756, agent12756, scalar12756, tp12756, tm12756, ep12756, em12756, dsL]
  · norm_num [world12756, agent12756, scalar12756, tp12756, tm12756, ep12756, em12756, dsL]
  · norm_num [world12756, agent12756, scalar12756, tp12756, tm12756, ep12756, em12756, dsL]
  · norm_num [world12756, agent12756, scalar12756, tp12756, tm12756, ep12756, em12756, dsL]
  · norm_num [world12756, agent12756, scalar12756, tp12756, tm12756, ep12756, em12756, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12756, agent12756, tp12756, tm12756, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12756, agent12756, scalar12756, tp12756, tm12756, ep12756, em12756, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12756, agent12756, tp12756, tm12756, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12756, agent12756, scalar12756, tp12756, tm12756, ep12756, em12756, dsL]

theorem negative12756 :
    Eminus aL (agent12756.root+dsL) scalar12756.worldRadius world12756.frame
      agent12756.frame tm12756 ≤ -em12756 := by
  apply negative_check (lo := (8552143444295035787 / 12500000000000000000)) (hi := (68417147554360286297 / 100000000000000000000))
    (y := (-((35840773818817210333 / 50000000000000000000)))) (u := (9766096015273837137 / 20000000000000000000))
  · norm_num [world12756, agent12756, scalar12756, tp12756, tm12756, ep12756, em12756, dsL]
  · norm_num [world12756, agent12756, scalar12756, tp12756, tm12756, ep12756, em12756, dsL]
  · norm_num [world12756, agent12756, scalar12756, tp12756, tm12756, ep12756, em12756, dsL]
  · norm_num [world12756, agent12756, scalar12756, tp12756, tm12756, ep12756, em12756, dsL]
  · norm_num [world12756, agent12756, scalar12756, tp12756, tm12756, ep12756, em12756, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12756, agent12756, tp12756, tm12756, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12756, agent12756, tp12756, tm12756, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12756, agent12756, scalar12756, tp12756, tm12756, ep12756, em12756, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12756, agent12756, tp12756, tm12756, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12756, agent12756, scalar12756, tp12756, tm12756, ep12756, em12756, dsL]

theorem tails12756 :
    exp (-((12756:ℝ)*ep12756)) ≤ scalar12756.upperTail ∧
    exp (-((12756:ℝ)*em12756)) ≤ scalar12756.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12756:ℝ)) (by norm_num [ep12756]) ?_)
      (show bp12756^8 ≤ scalar12756.upperTail by norm_num [bp12756, scalar12756])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12756, bp12756, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12756:ℝ)) (by norm_num [em12756]) ?_)
      (show bm12756^8 ≤ scalar12756.lowerTail by norm_num [bm12756, scalar12756])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12756, bm12756, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12756 :
    agent12756.root+dsL+scalar12756.worldRadius < √(1/100/aL) ∧
    2*(agent12756.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12756, agent12756, scalar12756, tp12756, tm12756, ep12756, em12756, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12756, agent12756, scalar12756, tp12756, tm12756, ep12756, em12756, dsL]

noncomputable def master12756 : MasterCertificate 12756 world12756 agent12756 :=
  master scalar12756 dsL tp12756 tm12756 ep12756 em12756
    (by norm_num [dsL]) (by norm_num [tp12756]) (by norm_num [tm12756])
    (by norm_num [ep12756]) (by norm_num [em12756])
    positive12756 negative12756 tails12756.1 tails12756.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12756.1 tailGuards12756.2

theorem preserves12756 : master12756.toScalarCertificate = scalar12756 := rfl

noncomputable def tp12757 : ℝ := (2321670337 / 10000000000)
noncomputable def tm12757 : ℝ := (-((759291891 / 1250000000)))
noncomputable def ep12757 : ℝ := (51579411996597053 / 100000000000000000000)
noncomputable def em12757 : ℝ := (1004878856520847 / 2000000000000000000)
noncomputable def bp12757 : ℝ := (21966637100367281713 / 50000000000000000000)
noncomputable def bm12757 : ℝ := (11219724569029775979 / 25000000000000000000)

theorem positive12757 :
    Eplus aL (agent12757.root+dsL) scalar12757.worldRadius world12757.frame
      agent12757.frame tp12757 ≤ -ep12757 := by
  apply positive_check (eT := (115611764643949259913 / 100000000000000000000)) (y := (37902389187204347791 / 100000000000000000000)) (u := (1141295264029232769 / 781250000000000000))
  · norm_num [world12757, agent12757, scalar12757, tp12757, tm12757, ep12757, em12757, dsL]
  · norm_num [world12757, agent12757, scalar12757, tp12757, tm12757, ep12757, em12757, dsL]
  · norm_num [world12757, agent12757, scalar12757, tp12757, tm12757, ep12757, em12757, dsL]
  · norm_num [world12757, agent12757, scalar12757, tp12757, tm12757, ep12757, em12757, dsL]
  · norm_num [world12757, agent12757, scalar12757, tp12757, tm12757, ep12757, em12757, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12757, agent12757, tp12757, tm12757, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12757, agent12757, scalar12757, tp12757, tm12757, ep12757, em12757, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12757, agent12757, tp12757, tm12757, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12757, agent12757, scalar12757, tp12757, tm12757, ep12757, em12757, dsL]

theorem negative12757 :
    Eminus aL (agent12757.root+dsL) scalar12757.worldRadius world12757.frame
      agent12757.frame tm12757 ≤ -em12757 := by
  apply negative_check (lo := (34208477756987172521 / 50000000000000000000)) (hi := (68416955513974345043 / 100000000000000000000))
    (y := (-((3584079810495705731 / 5000000000000000000)))) (u := (9766091271659517459 / 20000000000000000000))
  · norm_num [world12757, agent12757, scalar12757, tp12757, tm12757, ep12757, em12757, dsL]
  · norm_num [world12757, agent12757, scalar12757, tp12757, tm12757, ep12757, em12757, dsL]
  · norm_num [world12757, agent12757, scalar12757, tp12757, tm12757, ep12757, em12757, dsL]
  · norm_num [world12757, agent12757, scalar12757, tp12757, tm12757, ep12757, em12757, dsL]
  · norm_num [world12757, agent12757, scalar12757, tp12757, tm12757, ep12757, em12757, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12757, agent12757, tp12757, tm12757, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12757, agent12757, tp12757, tm12757, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12757, agent12757, scalar12757, tp12757, tm12757, ep12757, em12757, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12757, agent12757, tp12757, tm12757, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12757, agent12757, scalar12757, tp12757, tm12757, ep12757, em12757, dsL]

theorem tails12757 :
    exp (-((12757:ℝ)*ep12757)) ≤ scalar12757.upperTail ∧
    exp (-((12757:ℝ)*em12757)) ≤ scalar12757.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12757:ℝ)) (by norm_num [ep12757]) ?_)
      (show bp12757^8 ≤ scalar12757.upperTail by norm_num [bp12757, scalar12757])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12757, bp12757, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12757:ℝ)) (by norm_num [em12757]) ?_)
      (show bm12757^8 ≤ scalar12757.lowerTail by norm_num [bm12757, scalar12757])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12757, bm12757, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12757 :
    agent12757.root+dsL+scalar12757.worldRadius < √(1/100/aL) ∧
    2*(agent12757.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12757, agent12757, scalar12757, tp12757, tm12757, ep12757, em12757, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12757, agent12757, scalar12757, tp12757, tm12757, ep12757, em12757, dsL]

noncomputable def master12757 : MasterCertificate 12757 world12757 agent12757 :=
  master scalar12757 dsL tp12757 tm12757 ep12757 em12757
    (by norm_num [dsL]) (by norm_num [tp12757]) (by norm_num [tm12757])
    (by norm_num [ep12757]) (by norm_num [em12757])
    positive12757 negative12757 tails12757.1 tails12757.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12757.1 tailGuards12757.2

theorem preserves12757 : master12757.toScalarCertificate = scalar12757 := rfl

noncomputable def tp12758 : ℝ := (2321753651 / 10000000000)
noncomputable def tm12758 : ℝ := (-((6074513367 / 10000000000)))
noncomputable def ep12758 : ℝ := (51581964281170319 / 100000000000000000000)
noncomputable def em12758 : ℝ := (2009845145191163 / 4000000000000000000)
noncomputable def bp12758 : ℝ := (21964326840755077953 / 50000000000000000000)
noncomputable def bm12758 : ℝ := (11218628870197445943 / 25000000000000000000)

theorem positive12758 :
    Eplus aL (agent12758.root+dsL) scalar12758.worldRadius world12758.frame
      agent12758.frame tp12758 ≤ -ep12758 := by
  apply positive_check (eT := (11561199831500160159 / 10000000000000000000)) (y := (7580632538202960847 / 20000000000000000000)) (u := (3652173094482339183 / 2500000000000000000))
  · norm_num [world12758, agent12758, scalar12758, tp12758, tm12758, ep12758, em12758, dsL]
  · norm_num [world12758, agent12758, scalar12758, tp12758, tm12758, ep12758, em12758, dsL]
  · norm_num [world12758, agent12758, scalar12758, tp12758, tm12758, ep12758, em12758, dsL]
  · norm_num [world12758, agent12758, scalar12758, tp12758, tm12758, ep12758, em12758, dsL]
  · norm_num [world12758, agent12758, scalar12758, tp12758, tm12758, ep12758, em12758, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12758, agent12758, tp12758, tm12758, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12758, agent12758, scalar12758, tp12758, tm12758, ep12758, em12758, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12758, agent12758, tp12758, tm12758, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12758, agent12758, scalar12758, tp12758, tm12758, ep12758, em12758, dsL]

theorem negative12758 :
    Eminus aL (agent12758.root+dsL) scalar12758.worldRadius world12758.frame
      agent12758.frame tm12758 ≤ -em12758 := by
  apply negative_check (lo := (68416763604713971689 / 100000000000000000000)) (hi := (6841676360471397169 / 10000000000000000000))
    (y := (-((35840822720867373149 / 50000000000000000000)))) (u := (24415216159090408521 / 50000000000000000000))
  · norm_num [world12758, agent12758, scalar12758, tp12758, tm12758, ep12758, em12758, dsL]
  · norm_num [world12758, agent12758, scalar12758, tp12758, tm12758, ep12758, em12758, dsL]
  · norm_num [world12758, agent12758, scalar12758, tp12758, tm12758, ep12758, em12758, dsL]
  · norm_num [world12758, agent12758, scalar12758, tp12758, tm12758, ep12758, em12758, dsL]
  · norm_num [world12758, agent12758, scalar12758, tp12758, tm12758, ep12758, em12758, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12758, agent12758, tp12758, tm12758, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12758, agent12758, tp12758, tm12758, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12758, agent12758, scalar12758, tp12758, tm12758, ep12758, em12758, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12758, agent12758, tp12758, tm12758, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12758, agent12758, scalar12758, tp12758, tm12758, ep12758, em12758, dsL]

theorem tails12758 :
    exp (-((12758:ℝ)*ep12758)) ≤ scalar12758.upperTail ∧
    exp (-((12758:ℝ)*em12758)) ≤ scalar12758.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12758:ℝ)) (by norm_num [ep12758]) ?_)
      (show bp12758^8 ≤ scalar12758.upperTail by norm_num [bp12758, scalar12758])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12758, bp12758, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12758:ℝ)) (by norm_num [em12758]) ?_)
      (show bm12758^8 ≤ scalar12758.lowerTail by norm_num [bm12758, scalar12758])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12758, bm12758, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12758 :
    agent12758.root+dsL+scalar12758.worldRadius < √(1/100/aL) ∧
    2*(agent12758.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12758, agent12758, scalar12758, tp12758, tm12758, ep12758, em12758, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12758, agent12758, scalar12758, tp12758, tm12758, ep12758, em12758, dsL]

noncomputable def master12758 : MasterCertificate 12758 world12758 agent12758 :=
  master scalar12758 dsL tp12758 tm12758 ep12758 em12758
    (by norm_num [dsL]) (by norm_num [tp12758]) (by norm_num [tm12758])
    (by norm_num [ep12758]) (by norm_num [em12758])
    positive12758 negative12758 tails12758.1 tails12758.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12758.1 tailGuards12758.2

theorem preserves12758 : master12758.toScalarCertificate = scalar12758 := rfl

noncomputable def tp12759 : ℝ := (232183689 / 1000000000)
noncomputable def tm12759 : ℝ := (-((3037345797 / 5000000000)))
noncomputable def ep12759 : ℝ := (25792257666583577 / 50000000000000000000)
noncomputable def em12759 : ℝ := (50248313294878567 / 100000000000000000000)
noncomputable def bp12759 : ℝ := (21962017115713071827 / 50000000000000000000)
noncomputable def bm12759 : ℝ := (22435066841558927979 / 50000000000000000000)

theorem positive12759 :
    Eplus aL (agent12759.root+dsL) scalar12759.worldRadius world12759.frame
      agent12759.frame tp12759 ≤ -ep12759 := by
  apply positive_check (eT := (115612231477091483553 / 100000000000000000000)) (y := (37903935085549292357 / 100000000000000000000)) (u := (18261006518883271969 / 12500000000000000000))
  · norm_num [world12759, agent12759, scalar12759, tp12759, tm12759, ep12759, em12759, dsL]
  · norm_num [world12759, agent12759, scalar12759, tp12759, tm12759, ep12759, em12759, dsL]
  · norm_num [world12759, agent12759, scalar12759, tp12759, tm12759, ep12759, em12759, dsL]
  · norm_num [world12759, agent12759, scalar12759, tp12759, tm12759, ep12759, em12759, dsL]
  · norm_num [world12759, agent12759, scalar12759, tp12759, tm12759, ep12759, em12759, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12759, agent12759, tp12759, tm12759, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12759, agent12759, scalar12759, tp12759, tm12759, ep12759, em12759, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12759, agent12759, tp12759, tm12759, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12759, agent12759, scalar12759, tp12759, tm12759, ep12759, em12759, dsL]

theorem negative12759 :
    Eminus aL (agent12759.root+dsL) scalar12759.worldRadius world12759.frame
      agent12759.frame tm12759 ≤ -em12759 := by
  apply negative_check (lo := (2736662867590611677 / 4000000000000000000)) (hi := (34208285844882645963 / 50000000000000000000))
    (y := (-((14336338937618898713 / 20000000000000000000)))) (u := (762975129234005823 / 1562500000000000000))
  · norm_num [world12759, agent12759, scalar12759, tp12759, tm12759, ep12759, em12759, dsL]
  · norm_num [world12759, agent12759, scalar12759, tp12759, tm12759, ep12759, em12759, dsL]
  · norm_num [world12759, agent12759, scalar12759, tp12759, tm12759, ep12759, em12759, dsL]
  · norm_num [world12759, agent12759, scalar12759, tp12759, tm12759, ep12759, em12759, dsL]
  · norm_num [world12759, agent12759, scalar12759, tp12759, tm12759, ep12759, em12759, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12759, agent12759, tp12759, tm12759, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12759, agent12759, tp12759, tm12759, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12759, agent12759, scalar12759, tp12759, tm12759, ep12759, em12759, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12759, agent12759, tp12759, tm12759, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12759, agent12759, scalar12759, tp12759, tm12759, ep12759, em12759, dsL]

theorem tails12759 :
    exp (-((12759:ℝ)*ep12759)) ≤ scalar12759.upperTail ∧
    exp (-((12759:ℝ)*em12759)) ≤ scalar12759.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12759:ℝ)) (by norm_num [ep12759]) ?_)
      (show bp12759^8 ≤ scalar12759.upperTail by norm_num [bp12759, scalar12759])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12759, bp12759, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12759:ℝ)) (by norm_num [em12759]) ?_)
      (show bm12759^8 ≤ scalar12759.lowerTail by norm_num [bm12759, scalar12759])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12759, bm12759, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12759 :
    agent12759.root+dsL+scalar12759.worldRadius < √(1/100/aL) ∧
    2*(agent12759.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12759, agent12759, scalar12759, tp12759, tm12759, ep12759, em12759, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12759, agent12759, scalar12759, tp12759, tm12759, ep12759, em12759, dsL]

noncomputable def master12759 : MasterCertificate 12759 world12759 agent12759 :=
  master scalar12759 dsL tp12759 tm12759 ep12759 em12759
    (by norm_num [dsL]) (by norm_num [tp12759]) (by norm_num [tm12759])
    (by norm_num [ep12759]) (by norm_num [em12759])
    positive12759 negative12759 tails12759.1 tails12759.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12759.1 tailGuards12759.2

theorem preserves12759 : master12759.toScalarCertificate = scalar12759 := rfl

noncomputable def tp12760 : ℝ := (2321993967 / 10000000000)
noncomputable def tm12760 : ℝ := (-((3037546541 / 5000000000)))
noncomputable def ep12760 : ℝ := (25794236754880989 / 50000000000000000000)
noncomputable def em12760 : ℝ := (10050406330542877 / 20000000000000000000)
noncomputable def bp12760 : ℝ := (43918429286651889687 / 100000000000000000000)
noncomputable def bm12760 : ℝ := (44864654557756372063 / 100000000000000000000)

theorem positive12760 :
    Eplus aL (agent12760.root+dsL) scalar12760.worldRadius world12760.frame
      agent12760.frame tp12760 ≤ -ep12760 := by
  apply positive_check (eT := (115612998039638373861 / 100000000000000000000)) (y := (37903984503584205369 / 100000000000000000000)) (u := (73044062172464314949 / 50000000000000000000))
  · norm_num [world12760, agent12760, scalar12760, tp12760, tm12760, ep12760, em12760, dsL]
  · norm_num [world12760, agent12760, scalar12760, tp12760, tm12760, ep12760, em12760, dsL]
  · norm_num [world12760, agent12760, scalar12760, tp12760, tm12760, ep12760, em12760, dsL]
  · norm_num [world12760, agent12760, scalar12760, tp12760, tm12760, ep12760, em12760, dsL]
  · norm_num [world12760, agent12760, scalar12760, tp12760, tm12760, ep12760, em12760, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12760, agent12760, tp12760, tm12760, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12760, agent12760, scalar12760, tp12760, tm12760, ep12760, em12760, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12760, agent12760, tp12760, tm12760, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12760, agent12760, scalar12760, tp12760, tm12760, ep12760, em12760, dsL]

theorem negative12760 :
    Eminus aL (agent12760.root+dsL) scalar12760.worldRadius world12760.frame
      agent12760.frame tm12760 ≤ -em12760 := by
  apply negative_check (lo := (34207712680271386899 / 50000000000000000000)) (hi := (68415425360542773799 / 100000000000000000000))
    (y := (-((71679843859929213159 / 100000000000000000000)))) (u := (48831312046289511539 / 100000000000000000000))
  · norm_num [world12760, agent12760, scalar12760, tp12760, tm12760, ep12760, em12760, dsL]
  · norm_num [world12760, agent12760, scalar12760, tp12760, tm12760, ep12760, em12760, dsL]
  · norm_num [world12760, agent12760, scalar12760, tp12760, tm12760, ep12760, em12760, dsL]
  · norm_num [world12760, agent12760, scalar12760, tp12760, tm12760, ep12760, em12760, dsL]
  · norm_num [world12760, agent12760, scalar12760, tp12760, tm12760, ep12760, em12760, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12760, agent12760, tp12760, tm12760, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12760, agent12760, tp12760, tm12760, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12760, agent12760, scalar12760, tp12760, tm12760, ep12760, em12760, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12760, agent12760, tp12760, tm12760, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12760, agent12760, scalar12760, tp12760, tm12760, ep12760, em12760, dsL]

theorem tails12760 :
    exp (-((12760:ℝ)*ep12760)) ≤ scalar12760.upperTail ∧
    exp (-((12760:ℝ)*em12760)) ≤ scalar12760.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12760:ℝ)) (by norm_num [ep12760]) ?_)
      (show bp12760^8 ≤ scalar12760.upperTail by norm_num [bp12760, scalar12760])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12760, bp12760, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12760:ℝ)) (by norm_num [em12760]) ?_)
      (show bm12760^8 ≤ scalar12760.lowerTail by norm_num [bm12760, scalar12760])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12760, bm12760, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12760 :
    agent12760.root+dsL+scalar12760.worldRadius < √(1/100/aL) ∧
    2*(agent12760.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12760, agent12760, scalar12760, tp12760, tm12760, ep12760, em12760, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12760, agent12760, scalar12760, tp12760, tm12760, ep12760, em12760, dsL]

noncomputable def master12760 : MasterCertificate 12760 world12760 agent12760 :=
  master scalar12760 dsL tp12760 tm12760 ep12760 em12760
    (by norm_num [dsL]) (by norm_num [tp12760]) (by norm_num [tm12760])
    (by norm_num [ep12760]) (by norm_num [em12760])
    positive12760 negative12760 tails12760.1 tails12760.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12760.1 tailGuards12760.2

theorem preserves12760 : master12760.toScalarCertificate = scalar12760 := rfl

noncomputable def tp12761 : ℝ := (2322077129 / 10000000000)
noncomputable def tm12761 : ℝ := (-((3037635553 / 5000000000)))
noncomputable def ep12761 : ℝ := (51591021474767353 / 100000000000000000000)
noncomputable def em12761 : ℝ := (50254213446746547 / 100000000000000000000)
noncomputable def bp12761 : ℝ := (21956906218374489357 / 50000000000000000000)
noncomputable def bm12761 : ℝ := (44860275201405222233 / 100000000000000000000)

theorem positive12761 :
    Eplus aL (agent12761.root+dsL) scalar12761.worldRadius world12761.frame
      agent12761.frame tp12761 ≤ -ep12761 := by
  apply positive_check (eT := (11561323070050108919 / 10000000000000000000)) (y := (9476189108966319481 / 25000000000000000000)) (u := (2921785041013436371 / 2000000000000000000))
  · norm_num [world12761, agent12761, scalar12761, tp12761, tm12761, ep12761, em12761, dsL]
  · norm_num [world12761, agent12761, scalar12761, tp12761, tm12761, ep12761, em12761, dsL]
  · norm_num [world12761, agent12761, scalar12761, tp12761, tm12761, ep12761, em12761, dsL]
  · norm_num [world12761, agent12761, scalar12761, tp12761, tm12761, ep12761, em12761, dsL]
  · norm_num [world12761, agent12761, scalar12761, tp12761, tm12761, ep12761, em12761, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12761, agent12761, tp12761, tm12761, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12761, agent12761, scalar12761, tp12761, tm12761, ep12761, em12761, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12761, agent12761, tp12761, tm12761, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12761, agent12761, scalar12761, tp12761, tm12761, ep12761, em12761, dsL]

theorem negative12761 :
    Eminus aL (agent12761.root+dsL) scalar12761.worldRadius world12761.frame
      agent12761.frame tm12761 ≤ -em12761 := by
  apply negative_check (lo := (68415234223061670241 / 100000000000000000000)) (hi := (34207617111530835121 / 50000000000000000000))
    (y := (-((17919973140598250787 / 25000000000000000000)))) (u := (1220782206606080881 / 2500000000000000000))
  · norm_num [world12761, agent12761, scalar12761, tp12761, tm12761, ep12761, em12761, dsL]
  · norm_num [world12761, agent12761, scalar12761, tp12761, tm12761, ep12761, em12761, dsL]
  · norm_num [world12761, agent12761, scalar12761, tp12761, tm12761, ep12761, em12761, dsL]
  · norm_num [world12761, agent12761, scalar12761, tp12761, tm12761, ep12761, em12761, dsL]
  · norm_num [world12761, agent12761, scalar12761, tp12761, tm12761, ep12761, em12761, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12761, agent12761, tp12761, tm12761, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12761, agent12761, tp12761, tm12761, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12761, agent12761, scalar12761, tp12761, tm12761, ep12761, em12761, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12761, agent12761, tp12761, tm12761, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12761, agent12761, scalar12761, tp12761, tm12761, ep12761, em12761, dsL]

theorem tails12761 :
    exp (-((12761:ℝ)*ep12761)) ≤ scalar12761.upperTail ∧
    exp (-((12761:ℝ)*em12761)) ≤ scalar12761.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12761:ℝ)) (by norm_num [ep12761]) ?_)
      (show bp12761^8 ≤ scalar12761.upperTail by norm_num [bp12761, scalar12761])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12761, bp12761, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12761:ℝ)) (by norm_num [em12761]) ?_)
      (show bm12761^8 ≤ scalar12761.lowerTail by norm_num [bm12761, scalar12761])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12761, bm12761, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12761 :
    agent12761.root+dsL+scalar12761.worldRadius < √(1/100/aL) ∧
    2*(agent12761.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12761, agent12761, scalar12761, tp12761, tm12761, ep12761, em12761, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12761, agent12761, scalar12761, tp12761, tm12761, ep12761, em12761, dsL]

noncomputable def master12761 : MasterCertificate 12761 world12761 agent12761 :=
  master scalar12761 dsL tp12761 tm12761 ep12761 em12761
    (by norm_num [dsL]) (by norm_num [tp12761]) (by norm_num [tm12761])
    (by norm_num [ep12761]) (by norm_num [em12761])
    positive12761 negative12761 tails12761.1 tails12761.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12761.1 tailGuards12761.2

theorem preserves12761 : master12761.toScalarCertificate = scalar12761 := rfl

noncomputable def tp12762 : ℝ := (232216023 / 1000000000)
noncomputable def tm12762 : ℝ := (-((3037724587 / 5000000000)))
noncomputable def ep12762 : ℝ := (10318713649381187 / 20000000000000000000)
noncomputable def em12762 : ℝ := (50256394150627891 / 100000000000000000000)
noncomputable def bp12762 : ℝ := (4390919662804400197 / 10000000000000000000)
noncomputable def bm12762 : ℝ := (8971179361588206109 / 20000000000000000000)

theorem positive12762 :
    Eplus aL (agent12762.root+dsL) scalar12762.worldRadius world12762.frame
      agent12762.frame tp12762 ≤ -ep12762 := by
  apply positive_check (eT := (23122692590713561323 / 20000000000000000000)) (y := (37905527707623461131 / 100000000000000000000)) (u := (14609037880015977117 / 10000000000000000000))
  · norm_num [world12762, agent12762, scalar12762, tp12762, tm12762, ep12762, em12762, dsL]
  · norm_num [world12762, agent12762, scalar12762, tp12762, tm12762, ep12762, em12762, dsL]
  · norm_num [world12762, agent12762, scalar12762, tp12762, tm12762, ep12762, em12762, dsL]
  · norm_num [world12762, agent12762, scalar12762, tp12762, tm12762, ep12762, em12762, dsL]
  · norm_num [world12762, agent12762, scalar12762, tp12762, tm12762, ep12762, em12762, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12762, agent12762, tp12762, tm12762, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12762, agent12762, scalar12762, tp12762, tm12762, ep12762, em12762, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12762, agent12762, tp12762, tm12762, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12762, agent12762, scalar12762, tp12762, tm12762, ep12762, em12762, dsL]

theorem negative12762 :
    Eminus aL (agent12762.root+dsL) scalar12762.worldRadius world12762.frame
      agent12762.frame tm12762 ≤ -em12762 := by
  apply negative_check (lo := (68415042840534603047 / 100000000000000000000)) (hi := (8551880355066825381 / 12500000000000000000))
    (y := (-((71679942645457986573 / 100000000000000000000)))) (u := (762988497000680091 / 1562500000000000000))
  · norm_num [world12762, agent12762, scalar12762, tp12762, tm12762, ep12762, em12762, dsL]
  · norm_num [world12762, agent12762, scalar12762, tp12762, tm12762, ep12762, em12762, dsL]
  · norm_num [world12762, agent12762, scalar12762, tp12762, tm12762, ep12762, em12762, dsL]
  · norm_num [world12762, agent12762, scalar12762, tp12762, tm12762, ep12762, em12762, dsL]
  · norm_num [world12762, agent12762, scalar12762, tp12762, tm12762, ep12762, em12762, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12762, agent12762, tp12762, tm12762, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12762, agent12762, tp12762, tm12762, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12762, agent12762, scalar12762, tp12762, tm12762, ep12762, em12762, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12762, agent12762, tp12762, tm12762, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12762, agent12762, scalar12762, tp12762, tm12762, ep12762, em12762, dsL]

theorem tails12762 :
    exp (-((12762:ℝ)*ep12762)) ≤ scalar12762.upperTail ∧
    exp (-((12762:ℝ)*em12762)) ≤ scalar12762.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12762:ℝ)) (by norm_num [ep12762]) ?_)
      (show bp12762^8 ≤ scalar12762.upperTail by norm_num [bp12762, scalar12762])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12762, bp12762, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12762:ℝ)) (by norm_num [em12762]) ?_)
      (show bm12762^8 ≤ scalar12762.lowerTail by norm_num [bm12762, scalar12762])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12762, bm12762, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12762 :
    agent12762.root+dsL+scalar12762.worldRadius < √(1/100/aL) ∧
    2*(agent12762.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12762, agent12762, scalar12762, tp12762, tm12762, ep12762, em12762, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12762, agent12762, scalar12762, tp12762, tm12762, ep12762, em12762, dsL]

noncomputable def master12762 : MasterCertificate 12762 world12762 agent12762 :=
  master scalar12762 dsL tp12762 tm12762 ep12762 em12762
    (by norm_num [dsL]) (by norm_num [tp12762]) (by norm_num [tm12762])
    (by norm_num [ep12762]) (by norm_num [em12762])
    positive12762 negative12762 tails12762.1 tails12762.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12762.1 tailGuards12762.2

theorem preserves12762 : master12762.toScalarCertificate = scalar12762 := rfl

noncomputable def tp12763 : ℝ := (2322243271 / 10000000000)
noncomputable def tm12763 : ℝ := (-((1215125373 / 2000000000)))
noncomputable def ep12763 : ℝ := (51596113171413763 / 100000000000000000000)
noncomputable def em12763 : ℝ := (25129286564886799 / 50000000000000000000)
noncomputable def bp12763 : ℝ := (10976145579782927277 / 25000000000000000000)
noncomputable def bm12763 : ℝ := (44851519831425780721 / 100000000000000000000)

theorem positive12763 :
    Eplus aL (agent12763.root+dsL) scalar12763.worldRadius world12763.frame
      agent12763.frame tp12763 ≤ -ep12763 := by
  apply positive_check (eT := (115613694806067593011 / 100000000000000000000)) (y := (37906298333529770281 / 100000000000000000000)) (u := (146091504614803334451 / 100000000000000000000))
  · norm_num [world12763, agent12763, scalar12763, tp12763, tm12763, ep12763, em12763, dsL]
  · norm_num [world12763, agent12763, scalar12763, tp12763, tm12763, ep12763, em12763, dsL]
  · norm_num [world12763, agent12763, scalar12763, tp12763, tm12763, ep12763, em12763, dsL]
  · norm_num [world12763, agent12763, scalar12763, tp12763, tm12763, ep12763, em12763, dsL]
  · norm_num [world12763, agent12763, scalar12763, tp12763, tm12763, ep12763, em12763, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12763, agent12763, tp12763, tm12763, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12763, agent12763, scalar12763, tp12763, tm12763, ep12763, em12763, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12763, agent12763, tp12763, tm12763, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12763, agent12763, scalar12763, tp12763, tm12763, ep12763, em12763, dsL]

theorem negative12763 :
    Eminus aL (agent12763.root+dsL) scalar12763.worldRadius world12763.frame
      agent12763.frame tm12763 ≤ -em12763 := by
  apply negative_check (lo := (1068982078320017777 / 1562500000000000000)) (hi := (68414853012481137729 / 100000000000000000000))
    (y := (-((35839994680091745127 / 50000000000000000000)))) (u := (6103905124582250757 / 12500000000000000000))
  · norm_num [world12763, agent12763, scalar12763, tp12763, tm12763, ep12763, em12763, dsL]
  · norm_num [world12763, agent12763, scalar12763, tp12763, tm12763, ep12763, em12763, dsL]
  · norm_num [world12763, agent12763, scalar12763, tp12763, tm12763, ep12763, em12763, dsL]
  · norm_num [world12763, agent12763, scalar12763, tp12763, tm12763, ep12763, em12763, dsL]
  · norm_num [world12763, agent12763, scalar12763, tp12763, tm12763, ep12763, em12763, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12763, agent12763, tp12763, tm12763, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12763, agent12763, tp12763, tm12763, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12763, agent12763, scalar12763, tp12763, tm12763, ep12763, em12763, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12763, agent12763, tp12763, tm12763, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12763, agent12763, scalar12763, tp12763, tm12763, ep12763, em12763, dsL]

theorem tails12763 :
    exp (-((12763:ℝ)*ep12763)) ≤ scalar12763.upperTail ∧
    exp (-((12763:ℝ)*em12763)) ≤ scalar12763.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12763:ℝ)) (by norm_num [ep12763]) ?_)
      (show bp12763^8 ≤ scalar12763.upperTail by norm_num [bp12763, scalar12763])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12763, bp12763, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12763:ℝ)) (by norm_num [em12763]) ?_)
      (show bm12763^8 ≤ scalar12763.lowerTail by norm_num [bm12763, scalar12763])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12763, bm12763, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12763 :
    agent12763.root+dsL+scalar12763.worldRadius < √(1/100/aL) ∧
    2*(agent12763.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12763, agent12763, scalar12763, tp12763, tm12763, ep12763, em12763, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12763, agent12763, scalar12763, tp12763, tm12763, ep12763, em12763, dsL]

noncomputable def master12763 : MasterCertificate 12763 world12763 agent12763 :=
  master scalar12763 dsL tp12763 tm12763 ep12763 em12763
    (by norm_num [dsL]) (by norm_num [tp12763]) (by norm_num [tm12763])
    (by norm_num [ep12763]) (by norm_num [em12763])
    positive12763 negative12763 tails12763.1 tails12763.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12763.1 tailGuards12763.2

theorem preserves12763 : master12763.toScalarCertificate = scalar12763 := rfl

noncomputable def tp12764 : ℝ := (580581581 / 2500000000)
noncomputable def tm12764 : ℝ := (-((6075804733 / 10000000000)))
noncomputable def ep12764 : ℝ := (51598657522962507 / 100000000000000000000)
noncomputable def em12764 : ℝ := (50260751609235297 / 100000000000000000000)
noncomputable def bp12764 : ℝ := (21949984308567379601 / 50000000000000000000)
noncomputable def bm12764 : ℝ := (44847143395249366679 / 100000000000000000000)

theorem positive12764 :
    Eplus aL (agent12764.root+dsL) scalar12764.worldRadius world12764.frame
      agent12764.frame tp12764 ≤ -ep12764 := by
  apply positive_check (eT := (115613926778083475257 / 100000000000000000000)) (y := (37907069377891802303 / 100000000000000000000)) (u := (73046315524727862251 / 50000000000000000000))
  · norm_num [world12764, agent12764, scalar12764, tp12764, tm12764, ep12764, em12764, dsL]
  · norm_num [world12764, agent12764, scalar12764, tp12764, tm12764, ep12764, em12764, dsL]
  · norm_num [world12764, agent12764, scalar12764, tp12764, tm12764, ep12764, em12764, dsL]
  · norm_num [world12764, agent12764, scalar12764, tp12764, tm12764, ep12764, em12764, dsL]
  · norm_num [world12764, agent12764, scalar12764, tp12764, tm12764, ep12764, em12764, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12764, agent12764, tp12764, tm12764, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12764, agent12764, scalar12764, tp12764, tm12764, ep12764, em12764, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12764, agent12764, tp12764, tm12764, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12764, agent12764, scalar12764, tp12764, tm12764, ep12764, em12764, dsL]

theorem negative12764 :
    Eminus aL (agent12764.root+dsL) scalar12764.worldRadius world12764.frame
      agent12764.frame tm12764 ≤ -em12764 := by
  apply negative_check (lo := (34207331185441045017 / 50000000000000000000)) (hi := (13682932474176418007 / 20000000000000000000))
    (y := (-((358400192930139851 / 500000000000000000)))) (u := (24415608479536585883 / 50000000000000000000))
  · norm_num [world12764, agent12764, scalar12764, tp12764, tm12764, ep12764, em12764, dsL]
  · norm_num [world12764, agent12764, scalar12764, tp12764, tm12764, ep12764, em12764, dsL]
  · norm_num [world12764, agent12764, scalar12764, tp12764, tm12764, ep12764, em12764, dsL]
  · norm_num [world12764, agent12764, scalar12764, tp12764, tm12764, ep12764, em12764, dsL]
  · norm_num [world12764, agent12764, scalar12764, tp12764, tm12764, ep12764, em12764, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12764, agent12764, tp12764, tm12764, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12764, agent12764, tp12764, tm12764, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12764, agent12764, scalar12764, tp12764, tm12764, ep12764, em12764, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12764, agent12764, tp12764, tm12764, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12764, agent12764, scalar12764, tp12764, tm12764, ep12764, em12764, dsL]

theorem tails12764 :
    exp (-((12764:ℝ)*ep12764)) ≤ scalar12764.upperTail ∧
    exp (-((12764:ℝ)*em12764)) ≤ scalar12764.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12764:ℝ)) (by norm_num [ep12764]) ?_)
      (show bp12764^8 ≤ scalar12764.upperTail by norm_num [bp12764, scalar12764])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12764, bp12764, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12764:ℝ)) (by norm_num [em12764]) ?_)
      (show bm12764^8 ≤ scalar12764.lowerTail by norm_num [bm12764, scalar12764])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12764, bm12764, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12764 :
    agent12764.root+dsL+scalar12764.worldRadius < √(1/100/aL) ∧
    2*(agent12764.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12764, agent12764, scalar12764, tp12764, tm12764, ep12764, em12764, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12764, agent12764, scalar12764, tp12764, tm12764, ep12764, em12764, dsL]

noncomputable def master12764 : MasterCertificate 12764 world12764 agent12764 :=
  master scalar12764 dsL tp12764 tm12764 ep12764 em12764
    (by norm_num [dsL]) (by norm_num [tp12764]) (by norm_num [tm12764])
    (by norm_num [ep12764]) (by norm_num [em12764])
    positive12764 negative12764 tails12764.1 tails12764.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12764.1 tailGuards12764.2

theorem preserves12764 : master12764.toScalarCertificate = scalar12764 := rfl

noncomputable def tp12765 : ℝ := (92896371 / 400000000)
noncomputable def tm12765 : ℝ := (-((6075982269 / 10000000000)))
noncomputable def ep12765 : ℝ := (51601200215111003 / 100000000000000000000)
noncomputable def em12765 : ℝ := (12565732126103657 / 25000000000000000000)
noncomputable def bp12765 : ℝ := (877907125660143277 / 2000000000000000000)
noncomputable def bm12765 : ℝ := (22421384137737714633 / 50000000000000000000)

theorem positive12765 :
    Eplus aL (agent12765.root+dsL) scalar12765.worldRadius world12765.frame
      agent12765.frame tp12765 ≤ -ep12765 := by
  apply positive_check (eT := (115614158046219688229 / 100000000000000000000)) (y := (4738479911774833967 / 12500000000000000000)) (u := (73046877922387647297 / 50000000000000000000))
  · norm_num [world12765, agent12765, scalar12765, tp12765, tm12765, ep12765, em12765, dsL]
  · norm_num [world12765, agent12765, scalar12765, tp12765, tm12765, ep12765, em12765, dsL]
  · norm_num [world12765, agent12765, scalar12765, tp12765, tm12765, ep12765, em12765, dsL]
  · norm_num [world12765, agent12765, scalar12765, tp12765, tm12765, ep12765, em12765, dsL]
  · norm_num [world12765, agent12765, scalar12765, tp12765, tm12765, ep12765, em12765, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12765, agent12765, tp12765, tm12765, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12765, agent12765, scalar12765, tp12765, tm12765, ep12765, em12765, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12765, agent12765, tp12765, tm12765, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12765, agent12765, scalar12765, tp12765, tm12765, ep12765, em12765, dsL]

theorem negative12765 :
    Eminus aL (agent12765.root+dsL) scalar12765.worldRadius world12765.frame
      agent12765.frame tm12765 ≤ -em12765 := by
  apply negative_check (lo := (34207236545643336129 / 50000000000000000000)) (hi := (68414473091286672259 / 100000000000000000000))
    (y := (-((71680085581789116099 / 100000000000000000000)))) (u := (48831194010476477479 / 100000000000000000000))
  · norm_num [world12765, agent12765, scalar12765, tp12765, tm12765, ep12765, em12765, dsL]
  · norm_num [world12765, agent12765, scalar12765, tp12765, tm12765, ep12765, em12765, dsL]
  · norm_num [world12765, agent12765, scalar12765, tp12765, tm12765, ep12765, em12765, dsL]
  · norm_num [world12765, agent12765, scalar12765, tp12765, tm12765, ep12765, em12765, dsL]
  · norm_num [world12765, agent12765, scalar12765, tp12765, tm12765, ep12765, em12765, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12765, agent12765, tp12765, tm12765, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12765, agent12765, tp12765, tm12765, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12765, agent12765, scalar12765, tp12765, tm12765, ep12765, em12765, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12765, agent12765, tp12765, tm12765, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12765, agent12765, scalar12765, tp12765, tm12765, ep12765, em12765, dsL]

theorem tails12765 :
    exp (-((12765:ℝ)*ep12765)) ≤ scalar12765.upperTail ∧
    exp (-((12765:ℝ)*em12765)) ≤ scalar12765.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12765:ℝ)) (by norm_num [ep12765]) ?_)
      (show bp12765^8 ≤ scalar12765.upperTail by norm_num [bp12765, scalar12765])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12765, bp12765, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12765:ℝ)) (by norm_num [em12765]) ?_)
      (show bm12765^8 ≤ scalar12765.lowerTail by norm_num [bm12765, scalar12765])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12765, bm12765, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12765 :
    agent12765.root+dsL+scalar12765.worldRadius < √(1/100/aL) ∧
    2*(agent12765.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12765, agent12765, scalar12765, tp12765, tm12765, ep12765, em12765, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12765, agent12765, scalar12765, tp12765, tm12765, ep12765, em12765, dsL]

noncomputable def master12765 : MasterCertificate 12765 world12765 agent12765 :=
  master scalar12765 dsL tp12765 tm12765 ep12765 em12765
    (by norm_num [dsL]) (by norm_num [tp12765]) (by norm_num [tm12765])
    (by norm_num [ep12765]) (by norm_num [em12765])
    positive12765 negative12765 tails12765.1 tails12765.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12765.1 tailGuards12765.2

theorem preserves12765 : master12765.toScalarCertificate = scalar12765 := rfl

noncomputable def tp12766 : ℝ := (290311533 / 1250000000)
noncomputable def tm12766 : ℝ := (-((607615983 / 1000000000)))
noncomputable def ep12766 : ℝ := (5160374186158881 / 10000000000000000000)
noncomputable def em12766 : ℝ := (50265104462437397 / 100000000000000000000)
noncomputable def bp12766 : ℝ := (1371585777713900927 / 3125000000000000000)
noncomputable def bm12766 : ℝ := (22419197004522134451 / 50000000000000000000)

theorem positive12766 :
    Eplus aL (agent12766.root+dsL) scalar12766.worldRadius world12766.frame
      agent12766.frame tp12766 ≤ -ep12766 := by
  apply positive_check (eT := (23122877924323089887 / 20000000000000000000)) (y := (189543050668061049 / 500000000000000000)) (u := (146094881997366472629 / 100000000000000000000))
  · norm_num [world12766, agent12766, scalar12766, tp12766, tm12766, ep12766, em12766, dsL]
  · norm_num [world12766, agent12766, scalar12766, tp12766, tm12766, ep12766, em12766, dsL]
  · norm_num [world12766, agent12766, scalar12766, tp12766, tm12766, ep12766, em12766, dsL]
  · norm_num [world12766, agent12766, scalar12766, tp12766, tm12766, ep12766, em12766, dsL]
  · norm_num [world12766, agent12766, scalar12766, tp12766, tm12766, ep12766, em12766, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12766, agent12766, tp12766, tm12766, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12766, agent12766, scalar12766, tp12766, tm12766, ep12766, em12766, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12766, agent12766, tp12766, tm12766, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12766, agent12766, scalar12766, tp12766, tm12766, ep12766, em12766, dsL]

theorem negative12766 :
    Eminus aL (agent12766.root+dsL) scalar12766.worldRadius world12766.frame
      agent12766.frame tm12766 ≤ -em12766 := by
  apply negative_check (lo := (34207141823951167609 / 50000000000000000000)) (hi := (68414283647902335219 / 100000000000000000000))
    (y := (-((71680133485623805307 / 100000000000000000000)))) (u := (48831170618467624769 / 100000000000000000000))
  · norm_num [world12766, agent12766, scalar12766, tp12766, tm12766, ep12766, em12766, dsL]
  · norm_num [world12766, agent12766, scalar12766, tp12766, tm12766, ep12766, em12766, dsL]
  · norm_num [world12766, agent12766, scalar12766, tp12766, tm12766, ep12766, em12766, dsL]
  · norm_num [world12766, agent12766, scalar12766, tp12766, tm12766, ep12766, em12766, dsL]
  · norm_num [world12766, agent12766, scalar12766, tp12766, tm12766, ep12766, em12766, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12766, agent12766, tp12766, tm12766, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12766, agent12766, tp12766, tm12766, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12766, agent12766, scalar12766, tp12766, tm12766, ep12766, em12766, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12766, agent12766, tp12766, tm12766, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12766, agent12766, scalar12766, tp12766, tm12766, ep12766, em12766, dsL]

theorem tails12766 :
    exp (-((12766:ℝ)*ep12766)) ≤ scalar12766.upperTail ∧
    exp (-((12766:ℝ)*em12766)) ≤ scalar12766.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12766:ℝ)) (by norm_num [ep12766]) ?_)
      (show bp12766^8 ≤ scalar12766.upperTail by norm_num [bp12766, scalar12766])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12766, bp12766, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12766:ℝ)) (by norm_num [em12766]) ?_)
      (show bm12766^8 ≤ scalar12766.lowerTail by norm_num [bm12766, scalar12766])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12766, bm12766, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12766 :
    agent12766.root+dsL+scalar12766.worldRadius < √(1/100/aL) ∧
    2*(agent12766.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12766, agent12766, scalar12766, tp12766, tm12766, ep12766, em12766, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12766, agent12766, scalar12766, tp12766, tm12766, ep12766, em12766, dsL]

noncomputable def master12766 : MasterCertificate 12766 world12766 agent12766 :=
  master scalar12766 dsL tp12766 tm12766 ep12766 em12766
    (by norm_num [dsL]) (by norm_num [tp12766]) (by norm_num [tm12766])
    (by norm_num [ep12766]) (by norm_num [em12766])
    positive12766 negative12766 tails12766.1 tails12766.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12766.1 tailGuards12766.2

theorem preserves12766 : master12766.toScalarCertificate = scalar12766 := rfl

noncomputable def tp12767 : ℝ := (2322575187 / 10000000000)
noncomputable def tm12767 : ℝ := (-((1519084337 / 2500000000)))
noncomputable def ep12767 : ℝ := (25803141069034213 / 50000000000000000000)
noncomputable def em12767 : ℝ := (5026727913763579 / 10000000000000000000)
noncomputable def bp12767 : ℝ := (8777226931154920259 / 20000000000000000000)
noncomputable def bm12767 : ℝ := (44834020843270558559 / 100000000000000000000)

theorem positive12767 :
    Eplus aL (agent12767.root+dsL) scalar12767.worldRadius world12767.frame
      agent12767.frame tp12767 ≤ -ep12767 := by
  apply positive_check (eT := (23122924150635041647 / 20000000000000000000)) (y := (37909380172326223763 / 100000000000000000000)) (u := (73048003494424237389 / 50000000000000000000))
  · norm_num [world12767, agent12767, scalar12767, tp12767, tm12767, ep12767, em12767, dsL]
  · norm_num [world12767, agent12767, scalar12767, tp12767, tm12767, ep12767, em12767, dsL]
  · norm_num [world12767, agent12767, scalar12767, tp12767, tm12767, ep12767, em12767, dsL]
  · norm_num [world12767, agent12767, scalar12767, tp12767, tm12767, ep12767, em12767, dsL]
  · norm_num [world12767, agent12767, scalar12767, tp12767, tm12767, ep12767, em12767, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12767, agent12767, tp12767, tm12767, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12767, agent12767, scalar12767, tp12767, tm12767, ep12767, em12767, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12767, agent12767, tp12767, tm12767, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12767, agent12767, scalar12767, tp12767, tm12767, ep12767, em12767, dsL]

theorem negative12767 :
    Eminus aL (agent12767.root+dsL) scalar12767.worldRadius world12767.frame
      agent12767.frame tm12767 ≤ -em12767 := by
  apply negative_check (lo := (34207047165634323923 / 50000000000000000000)) (hi := (68414094331268647847 / 100000000000000000000))
    (y := (-((71680181387884475961 / 100000000000000000000)))) (u := (48831147227238589043 / 100000000000000000000))
  · norm_num [world12767, agent12767, scalar12767, tp12767, tm12767, ep12767, em12767, dsL]
  · norm_num [world12767, agent12767, scalar12767, tp12767, tm12767, ep12767, em12767, dsL]
  · norm_num [world12767, agent12767, scalar12767, tp12767, tm12767, ep12767, em12767, dsL]
  · norm_num [world12767, agent12767, scalar12767, tp12767, tm12767, ep12767, em12767, dsL]
  · norm_num [world12767, agent12767, scalar12767, tp12767, tm12767, ep12767, em12767, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12767, agent12767, tp12767, tm12767, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12767, agent12767, tp12767, tm12767, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12767, agent12767, scalar12767, tp12767, tm12767, ep12767, em12767, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12767, agent12767, tp12767, tm12767, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12767, agent12767, scalar12767, tp12767, tm12767, ep12767, em12767, dsL]

theorem tails12767 :
    exp (-((12767:ℝ)*ep12767)) ≤ scalar12767.upperTail ∧
    exp (-((12767:ℝ)*em12767)) ≤ scalar12767.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12767:ℝ)) (by norm_num [ep12767]) ?_)
      (show bp12767^8 ≤ scalar12767.upperTail by norm_num [bp12767, scalar12767])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12767, bp12767, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12767:ℝ)) (by norm_num [em12767]) ?_)
      (show bm12767^8 ≤ scalar12767.lowerTail by norm_num [bm12767, scalar12767])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12767, bm12767, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12767 :
    agent12767.root+dsL+scalar12767.worldRadius < √(1/100/aL) ∧
    2*(agent12767.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12767, agent12767, scalar12767, tp12767, tm12767, ep12767, em12767, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12767, agent12767, scalar12767, tp12767, tm12767, ep12767, em12767, dsL]

noncomputable def master12767 : MasterCertificate 12767 world12767 agent12767 :=
  master scalar12767 dsL tp12767 tm12767 ep12767 em12767
    (by norm_num [dsL]) (by norm_num [tp12767]) (by norm_num [tm12767])
    (by norm_num [ep12767]) (by norm_num [em12767])
    positive12767 negative12767 tails12767.1 tails12767.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12767.1 tailGuards12767.2

theorem preserves12767 : master12767.toScalarCertificate = scalar12767 := rfl

noncomputable def tp12768 : ℝ := (2322658051 / 10000000000)
noncomputable def tm12768 : ℝ := (-((30382573 / 50000000)))
noncomputable def ep12768 : ℝ := (12902205188417501 / 25000000000000000000)
noncomputable def em12768 : ℝ := (50269452289390111 / 100000000000000000000)
noncomputable def bp12768 : ℝ := (21940762896736998861 / 50000000000000000000)
noncomputable def bm12768 : ℝ := (44829648950290002433 / 100000000000000000000)

theorem positive12768 :
    Eplus aL (agent12768.root+dsL) scalar12768.worldRadius world12768.frame
      agent12768.frame tp12768 ≤ -ep12768 := by
  apply positive_check (eT := (115614851491463533469 / 100000000000000000000)) (y := (9477537408446260937 / 25000000000000000000)) (u := (146097131145640099997 / 100000000000000000000))
  · norm_num [world12768, agent12768, scalar12768, tp12768, tm12768, ep12768, em12768, dsL]
  · norm_num [world12768, agent12768, scalar12768, tp12768, tm12768, ep12768, em12768, dsL]
  · norm_num [world12768, agent12768, scalar12768, tp12768, tm12768, ep12768, em12768, dsL]
  · norm_num [world12768, agent12768, scalar12768, tp12768, tm12768, ep12768, em12768, dsL]
  · norm_num [world12768, agent12768, scalar12768, tp12768, tm12768, ep12768, em12768, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12768, agent12768, tp12768, tm12768, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12768, agent12768, scalar12768, tp12768, tm12768, ep12768, em12768, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12768, agent12768, tp12768, tm12768, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12768, agent12768, scalar12768, tp12768, tm12768, ep12768, em12768, dsL]

theorem negative12768 :
    Eminus aL (agent12768.root+dsL) scalar12768.worldRadius world12768.frame
      agent12768.frame tm12768 ≤ -em12768 := by
  apply negative_check (lo := (13682781218890533213 / 20000000000000000000)) (hi := (34206953047226333033 / 50000000000000000000))
    (y := (-((35840113767038575193 / 50000000000000000000)))) (u := (24415562346764251827 / 50000000000000000000))
  · norm_num [world12768, agent12768, scalar12768, tp12768, tm12768, ep12768, em12768, dsL]
  · norm_num [world12768, agent12768, scalar12768, tp12768, tm12768, ep12768, em12768, dsL]
  · norm_num [world12768, agent12768, scalar12768, tp12768, tm12768, ep12768, em12768, dsL]
  · norm_num [world12768, agent12768, scalar12768, tp12768, tm12768, ep12768, em12768, dsL]
  · norm_num [world12768, agent12768, scalar12768, tp12768, tm12768, ep12768, em12768, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12768, agent12768, tp12768, tm12768, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12768, agent12768, tp12768, tm12768, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12768, agent12768, scalar12768, tp12768, tm12768, ep12768, em12768, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12768, agent12768, tp12768, tm12768, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12768, agent12768, scalar12768, tp12768, tm12768, ep12768, em12768, dsL]

theorem tails12768 :
    exp (-((12768:ℝ)*ep12768)) ≤ scalar12768.upperTail ∧
    exp (-((12768:ℝ)*em12768)) ≤ scalar12768.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12768:ℝ)) (by norm_num [ep12768]) ?_)
      (show bp12768^8 ≤ scalar12768.upperTail by norm_num [bp12768, scalar12768])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12768, bp12768, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12768:ℝ)) (by norm_num [em12768]) ?_)
      (show bm12768^8 ≤ scalar12768.lowerTail by norm_num [bm12768, scalar12768])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12768, bm12768, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12768 :
    agent12768.root+dsL+scalar12768.worldRadius < √(1/100/aL) ∧
    2*(agent12768.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12768, agent12768, scalar12768, tp12768, tm12768, ep12768, em12768, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12768, agent12768, scalar12768, tp12768, tm12768, ep12768, em12768, dsL]

noncomputable def master12768 : MasterCertificate 12768 world12768 agent12768 :=
  master scalar12768 dsL tp12768 tm12768 ep12768 em12768
    (by norm_num [dsL]) (by norm_num [tp12768]) (by norm_num [tm12768])
    (by norm_num [ep12768]) (by norm_num [em12768])
    positive12768 negative12768 tails12768.1 tails12768.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12768.1 tailGuards12768.2

theorem preserves12768 : master12768.toScalarCertificate = scalar12768 := rfl

noncomputable def tp12769 : ℝ := (2322740921 / 10000000000)
noncomputable def tm12769 : ℝ := (-((6076691813 / 10000000000)))
noncomputable def ep12769 : ℝ := (51611358159198143 / 100000000000000000000)
noncomputable def em12769 : ℝ := (12567906082337759 / 25000000000000000000)
noncomputable def bp12769 : ℝ := (877538359683491353 / 2000000000000000000)
noncomputable def bm12769 : ℝ := (44825278035546849011 / 100000000000000000000)

theorem positive12769 :
    Eplus aL (agent12769.root+dsL) scalar12769.worldRadius world12769.frame
      agent12769.frame tp12769 ≤ -ep12769 := by
  apply positive_check (eT := (57807541152951015921 / 50000000000000000000)) (y := (37910919506728138467 / 100000000000000000000)) (u := (29219651182450611849 / 20000000000000000000))
  · norm_num [world12769, agent12769, scalar12769, tp12769, tm12769, ep12769, em12769, dsL]
  · norm_num [world12769, agent12769, scalar12769, tp12769, tm12769, ep12769, em12769, dsL]
  · norm_num [world12769, agent12769, scalar12769, tp12769, tm12769, ep12769, em12769, dsL]
  · norm_num [world12769, agent12769, scalar12769, tp12769, tm12769, ep12769, em12769, dsL]
  · norm_num [world12769, agent12769, scalar12769, tp12769, tm12769, ep12769, em12769, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12769, agent12769, tp12769, tm12769, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12769, agent12769, scalar12769, tp12769, tm12769, ep12769, em12769, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12769, agent12769, tp12769, tm12769, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12769, agent12769, scalar12769, tp12769, tm12769, ep12769, em12769, dsL]

theorem negative12769 :
    Eminus aL (agent12769.root+dsL) scalar12769.worldRadius world12769.frame
      agent12769.frame tm12769 ≤ -em12769 := by
  apply negative_check (lo := (34206858983664122777 / 50000000000000000000)) (hi := (13682743593465649111 / 20000000000000000000))
    (y := (-((35840136920896959129 / 50000000000000000000)))) (u := (12207775520238705423 / 25000000000000000000))
  · norm_num [world12769, agent12769, scalar12769, tp12769, tm12769, ep12769, em12769, dsL]
  · norm_num [world12769, agent12769, scalar12769, tp12769, tm12769, ep12769, em12769, dsL]
  · norm_num [world12769, agent12769, scalar12769, tp12769, tm12769, ep12769, em12769, dsL]
  · norm_num [world12769, agent12769, scalar12769, tp12769, tm12769, ep12769, em12769, dsL]
  · norm_num [world12769, agent12769, scalar12769, tp12769, tm12769, ep12769, em12769, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12769, agent12769, tp12769, tm12769, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12769, agent12769, tp12769, tm12769, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12769, agent12769, scalar12769, tp12769, tm12769, ep12769, em12769, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12769, agent12769, tp12769, tm12769, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12769, agent12769, scalar12769, tp12769, tm12769, ep12769, em12769, dsL]

theorem tails12769 :
    exp (-((12769:ℝ)*ep12769)) ≤ scalar12769.upperTail ∧
    exp (-((12769:ℝ)*em12769)) ≤ scalar12769.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12769:ℝ)) (by norm_num [ep12769]) ?_)
      (show bp12769^8 ≤ scalar12769.upperTail by norm_num [bp12769, scalar12769])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12769, bp12769, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12769:ℝ)) (by norm_num [em12769]) ?_)
      (show bm12769^8 ≤ scalar12769.lowerTail by norm_num [bm12769, scalar12769])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12769, bm12769, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12769 :
    agent12769.root+dsL+scalar12769.worldRadius < √(1/100/aL) ∧
    2*(agent12769.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12769, agent12769, scalar12769, tp12769, tm12769, ep12769, em12769, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12769, agent12769, scalar12769, tp12769, tm12769, ep12769, em12769, dsL]

noncomputable def master12769 : MasterCertificate 12769 world12769 agent12769 :=
  master scalar12769 dsL tp12769 tm12769 ep12769 em12769
    (by norm_num [dsL]) (by norm_num [tp12769]) (by norm_num [tm12769])
    (by norm_num [ep12769]) (by norm_num [em12769])
    positive12769 negative12769 tails12769.1 tails12769.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12769.1 tailGuards12769.2

theorem preserves12769 : master12769.toScalarCertificate = scalar12769 := rfl

noncomputable def tp12770 : ℝ := (2322897453 / 10000000000)
noncomputable def tm12770 : ℝ := (-((759636529 / 1250000000)))
noncomputable def ep12770 : ℝ := (1612978186273613 / 3125000000000000000)
noncomputable def em12770 : ℝ := (50275329108986103 / 100000000000000000000)
noncomputable def bp12770 : ℝ := (43871325475801308161 / 100000000000000000000)
noncomputable def bm12770 : ℝ := (44819810712681735243 / 100000000000000000000)

theorem positive12770 :
    Eplus aL (agent12770.root+dsL) scalar12770.worldRadius world12770.frame
      agent12770.frame tp12770 ≤ -ep12770 := by
  apply positive_check (eT := (57807922572966602629 / 50000000000000000000)) (y := (37910964972416245133 / 100000000000000000000)) (u := (146098322336845521787 / 100000000000000000000))
  · norm_num [world12770, agent12770, scalar12770, tp12770, tm12770, ep12770, em12770, dsL]
  · norm_num [world12770, agent12770, scalar12770, tp12770, tm12770, ep12770, em12770, dsL]
  · norm_num [world12770, agent12770, scalar12770, tp12770, tm12770, ep12770, em12770, dsL]
  · norm_num [world12770, agent12770, scalar12770, tp12770, tm12770, ep12770, em12770, dsL]
  · norm_num [world12770, agent12770, scalar12770, tp12770, tm12770, ep12770, em12770, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12770, agent12770, tp12770, tm12770, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12770, agent12770, scalar12770, tp12770, tm12770, ep12770, em12770, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12770, agent12770, tp12770, tm12770, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12770, agent12770, scalar12770, tp12770, tm12770, ep12770, em12770, dsL]

theorem negative12770 :
    Eminus aL (agent12770.root+dsL) scalar12770.worldRadius world12770.frame
      agent12770.frame tm12770 ≤ -em12770 := by
  apply negative_check (lo := (8551571988736929829 / 12500000000000000000)) (hi := (68412575909895438633 / 100000000000000000000))
    (y := (-((35839211564866816859 / 50000000000000000000)))) (u := (48832005812412911527 / 100000000000000000000))
  · norm_num [world12770, agent12770, scalar12770, tp12770, tm12770, ep12770, em12770, dsL]
  · norm_num [world12770, agent12770, scalar12770, tp12770, tm12770, ep12770, em12770, dsL]
  · norm_num [world12770, agent12770, scalar12770, tp12770, tm12770, ep12770, em12770, dsL]
  · norm_num [world12770, agent12770, scalar12770, tp12770, tm12770, ep12770, em12770, dsL]
  · norm_num [world12770, agent12770, scalar12770, tp12770, tm12770, ep12770, em12770, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12770, agent12770, tp12770, tm12770, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12770, agent12770, tp12770, tm12770, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12770, agent12770, scalar12770, tp12770, tm12770, ep12770, em12770, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12770, agent12770, tp12770, tm12770, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12770, agent12770, scalar12770, tp12770, tm12770, ep12770, em12770, dsL]

theorem tails12770 :
    exp (-((12770:ℝ)*ep12770)) ≤ scalar12770.upperTail ∧
    exp (-((12770:ℝ)*em12770)) ≤ scalar12770.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12770:ℝ)) (by norm_num [ep12770]) ?_)
      (show bp12770^8 ≤ scalar12770.upperTail by norm_num [bp12770, scalar12770])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12770, bp12770, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12770:ℝ)) (by norm_num [em12770]) ?_)
      (show bm12770^8 ≤ scalar12770.lowerTail by norm_num [bm12770, scalar12770])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12770, bm12770, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12770 :
    agent12770.root+dsL+scalar12770.worldRadius < √(1/100/aL) ∧
    2*(agent12770.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12770, agent12770, scalar12770, tp12770, tm12770, ep12770, em12770, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12770, agent12770, scalar12770, tp12770, tm12770, ep12770, em12770, dsL]

noncomputable def master12770 : MasterCertificate 12770 world12770 agent12770 :=
  master scalar12770 dsL tp12770 tm12770 ep12770 em12770
    (by norm_num [dsL]) (by norm_num [tp12770]) (by norm_num [tm12770])
    (by norm_num [ep12770]) (by norm_num [em12770])
    positive12770 negative12770 tails12770.1 tails12770.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12770.1 tailGuards12770.2

theorem preserves12770 : master12770.toScalarCertificate = scalar12770 := rfl

noncomputable def tp12771 : ℝ := (11614901 / 50000000)
noncomputable def tm12771 : ℝ := (-((243090767 / 400000000)))
noncomputable def ep12771 : ℝ := (51617836601501233 / 100000000000000000000)
noncomputable def em12771 : ℝ := (12569374638301059 / 25000000000000000000)
noncomputable def bp12771 : ℝ := (877334400801038673 / 2000000000000000000)
noncomputable def bm12771 : ℝ := (22407721020828579687 / 50000000000000000000)

theorem positive12771 :
    Eplus aL (agent12771.root+dsL) scalar12771.worldRadius world12771.frame
      agent12771.frame tp12771 ≤ -ep12771 := by
  apply positive_check (eT := (5780803756357663763 / 5000000000000000000)) (y := (3791173357512605347 / 10000000000000000000)) (u := (146099445256825378469 / 100000000000000000000))
  · norm_num [world12771, agent12771, scalar12771, tp12771, tm12771, ep12771, em12771, dsL]
  · norm_num [world12771, agent12771, scalar12771, tp12771, tm12771, ep12771, em12771, dsL]
  · norm_num [world12771, agent12771, scalar12771, tp12771, tm12771, ep12771, em12771, dsL]
  · norm_num [world12771, agent12771, scalar12771, tp12771, tm12771, ep12771, em12771, dsL]
  · norm_num [world12771, agent12771, scalar12771, tp12771, tm12771, ep12771, em12771, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12771, agent12771, tp12771, tm12771, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12771, agent12771, scalar12771, tp12771, tm12771, ep12771, em12771, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12771, agent12771, tp12771, tm12771, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12771, agent12771, scalar12771, tp12771, tm12771, ep12771, em12771, dsL]

theorem negative12771 :
    Eminus aL (agent12771.root+dsL) scalar12771.worldRadius world12771.frame
      agent12771.frame tm12771 ≤ -em12771 := by
  apply negative_check (lo := (17103097211516794003 / 25000000000000000000)) (hi := (68412388846067176013 / 100000000000000000000))
    (y := (-((716784682423201799 / 1000000000000000000)))) (u := (3051998986439812261 / 6250000000000000000))
  · norm_num [world12771, agent12771, scalar12771, tp12771, tm12771, ep12771, em12771, dsL]
  · norm_num [world12771, agent12771, scalar12771, tp12771, tm12771, ep12771, em12771, dsL]
  · norm_num [world12771, agent12771, scalar12771, tp12771, tm12771, ep12771, em12771, dsL]
  · norm_num [world12771, agent12771, scalar12771, tp12771, tm12771, ep12771, em12771, dsL]
  · norm_num [world12771, agent12771, scalar12771, tp12771, tm12771, ep12771, em12771, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12771, agent12771, tp12771, tm12771, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12771, agent12771, tp12771, tm12771, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12771, agent12771, scalar12771, tp12771, tm12771, ep12771, em12771, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12771, agent12771, tp12771, tm12771, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12771, agent12771, scalar12771, tp12771, tm12771, ep12771, em12771, dsL]

theorem tails12771 :
    exp (-((12771:ℝ)*ep12771)) ≤ scalar12771.upperTail ∧
    exp (-((12771:ℝ)*em12771)) ≤ scalar12771.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12771:ℝ)) (by norm_num [ep12771]) ?_)
      (show bp12771^8 ≤ scalar12771.upperTail by norm_num [bp12771, scalar12771])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12771, bp12771, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12771:ℝ)) (by norm_num [em12771]) ?_)
      (show bm12771^8 ≤ scalar12771.lowerTail by norm_num [bm12771, scalar12771])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12771, bm12771, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12771 :
    agent12771.root+dsL+scalar12771.worldRadius < √(1/100/aL) ∧
    2*(agent12771.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12771, agent12771, scalar12771, tp12771, tm12771, ep12771, em12771, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12771, agent12771, scalar12771, tp12771, tm12771, ep12771, em12771, dsL]

noncomputable def master12771 : MasterCertificate 12771 world12771 agent12771 :=
  master scalar12771 dsL tp12771 tm12771 ep12771 em12771
    (by norm_num [dsL]) (by norm_num [tp12771]) (by norm_num [tm12771])
    (by norm_num [ep12771]) (by norm_num [em12771])
    positive12771 negative12771 tails12771.1 tails12771.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12771.1 tailGuards12771.2

theorem preserves12771 : master12771.toScalarCertificate = scalar12771 := rfl

noncomputable def tp12772 : ℝ := (1161531489 / 5000000000)
noncomputable def tm12772 : ℝ := (-((243097847 / 400000000)))
noncomputable def ep12772 : ℝ := (25810185100700481 / 50000000000000000000)
noncomputable def em12772 : ℝ := (25139833532319217 / 50000000000000000000)
noncomputable def bp12772 : ℝ := (21931057769343662499 / 50000000000000000000)
noncomputable def bm12772 : ℝ := (22405537110369580999 / 50000000000000000000)

theorem positive12772 :
    Eplus aL (agent12772.root+dsL) scalar12772.worldRadius world12772.frame
      agent12772.frame tp12772 ≤ -ep12772 := by
  apply positive_check (eT := (115616305365094474437 / 100000000000000000000)) (y := (9478125744299046187 / 25000000000000000000)) (u := (9131285584581627503 / 6250000000000000000))
  · norm_num [world12772, agent12772, scalar12772, tp12772, tm12772, ep12772, em12772, dsL]
  · norm_num [world12772, agent12772, scalar12772, tp12772, tm12772, ep12772, em12772, dsL]
  · norm_num [world12772, agent12772, scalar12772, tp12772, tm12772, ep12772, em12772, dsL]
  · norm_num [world12772, agent12772, scalar12772, tp12772, tm12772, ep12772, em12772, dsL]
  · norm_num [world12772, agent12772, scalar12772, tp12772, tm12772, ep12772, em12772, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12772, agent12772, tp12772, tm12772, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12772, agent12772, scalar12772, tp12772, tm12772, ep12772, em12772, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12772, agent12772, tp12772, tm12772, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12772, agent12772, scalar12772, tp12772, tm12772, ep12772, em12772, dsL]

theorem negative12772 :
    Eminus aL (agent12772.root+dsL) scalar12772.worldRadius world12772.frame
      agent12772.frame tm12772 ≤ -em12772 := by
  apply negative_check (lo := (1710305037040832033 / 2500000000000000000)) (hi := (68412201481633281321 / 100000000000000000000))
    (y := (-((71678514571398130213 / 100000000000000000000)))) (u := (6103995144954300657 / 12500000000000000000))
  · norm_num [world12772, agent12772, scalar12772, tp12772, tm12772, ep12772, em12772, dsL]
  · norm_num [world12772, agent12772, scalar12772, tp12772, tm12772, ep12772, em12772, dsL]
  · norm_num [world12772, agent12772, scalar12772, tp12772, tm12772, ep12772, em12772, dsL]
  · norm_num [world12772, agent12772, scalar12772, tp12772, tm12772, ep12772, em12772, dsL]
  · norm_num [world12772, agent12772, scalar12772, tp12772, tm12772, ep12772, em12772, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12772, agent12772, tp12772, tm12772, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12772, agent12772, tp12772, tm12772, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12772, agent12772, scalar12772, tp12772, tm12772, ep12772, em12772, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12772, agent12772, tp12772, tm12772, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12772, agent12772, scalar12772, tp12772, tm12772, ep12772, em12772, dsL]

theorem tails12772 :
    exp (-((12772:ℝ)*ep12772)) ≤ scalar12772.upperTail ∧
    exp (-((12772:ℝ)*em12772)) ≤ scalar12772.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12772:ℝ)) (by norm_num [ep12772]) ?_)
      (show bp12772^8 ≤ scalar12772.upperTail by norm_num [bp12772, scalar12772])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12772, bp12772, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12772:ℝ)) (by norm_num [em12772]) ?_)
      (show bm12772^8 ≤ scalar12772.lowerTail by norm_num [bm12772, scalar12772])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12772, bm12772, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12772 :
    agent12772.root+dsL+scalar12772.worldRadius < √(1/100/aL) ∧
    2*(agent12772.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12772, agent12772, scalar12772, tp12772, tm12772, ep12772, em12772, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12772, agent12772, scalar12772, tp12772, tm12772, ep12772, em12772, dsL]

noncomputable def master12772 : MasterCertificate 12772 world12772 agent12772 :=
  master scalar12772 dsL tp12772 tm12772 ep12772 em12772
    (by norm_num [dsL]) (by norm_num [tp12772]) (by norm_num [tm12772])
    (by norm_num [ep12772]) (by norm_num [em12772])
    positive12772 negative12772 tails12772.1 tails12772.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12772.1 tailGuards12772.2

theorem preserves12772 : master12772.toScalarCertificate = scalar12772 := rfl

noncomputable def tp12773 : ℝ := (145196601 / 625000000)
noncomputable def tm12773 : ℝ := (-((6077622959 / 10000000000)))
noncomputable def ep12773 : ℝ := (806607850491753 / 1562500000000000000)
noncomputable def em12773 : ℝ := (25140917146805063 / 50000000000000000000)
noncomputable def bp12773 : ℝ := (21928756101026351677 / 50000000000000000000)
noncomputable def bm12773 : ℝ := (22403353750038623333 / 50000000000000000000)

theorem positive12773 :
    Eplus aL (agent12773.root+dsL) scalar12773.worldRadius world12773.frame
      agent12773.frame tp12773 ≤ -ep12773 := by
  apply positive_check (eT := (115616534624845423171 / 100000000000000000000)) (y := (37913270280333762221 / 100000000000000000000)) (u := (73050845195929791507 / 50000000000000000000))
  · norm_num [world12773, agent12773, scalar12773, tp12773, tm12773, ep12773, em12773, dsL]
  · norm_num [world12773, agent12773, scalar12773, tp12773, tm12773, ep12773, em12773, dsL]
  · norm_num [world12773, agent12773, scalar12773, tp12773, tm12773, ep12773, em12773, dsL]
  · norm_num [world12773, agent12773, scalar12773, tp12773, tm12773, ep12773, em12773, dsL]
  · norm_num [world12773, agent12773, scalar12773, tp12773, tm12773, ep12773, em12773, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12773, agent12773, tp12773, tm12773, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12773, agent12773, scalar12773, tp12773, tm12773, ep12773, em12773, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12773, agent12773, tp12773, tm12773, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12773, agent12773, scalar12773, tp12773, tm12773, ep12773, em12773, dsL]

theorem negative12773 :
    Eminus aL (agent12773.root+dsL) scalar12773.worldRadius world12773.frame
      agent12773.frame tm12773 ≤ -em12773 := by
  apply negative_check (lo := (68412014983178395883 / 100000000000000000000)) (hi := (17103003745794598971 / 25000000000000000000))
    (y := (-((71678559219579697469 / 100000000000000000000)))) (u := (24415969678528295539 / 50000000000000000000))
  · norm_num [world12773, agent12773, scalar12773, tp12773, tm12773, ep12773, em12773, dsL]
  · norm_num [world12773, agent12773, scalar12773, tp12773, tm12773, ep12773, em12773, dsL]
  · norm_num [world12773, agent12773, scalar12773, tp12773, tm12773, ep12773, em12773, dsL]
  · norm_num [world12773, agent12773, scalar12773, tp12773, tm12773, ep12773, em12773, dsL]
  · norm_num [world12773, agent12773, scalar12773, tp12773, tm12773, ep12773, em12773, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12773, agent12773, tp12773, tm12773, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12773, agent12773, tp12773, tm12773, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12773, agent12773, scalar12773, tp12773, tm12773, ep12773, em12773, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12773, agent12773, tp12773, tm12773, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12773, agent12773, scalar12773, tp12773, tm12773, ep12773, em12773, dsL]

theorem tails12773 :
    exp (-((12773:ℝ)*ep12773)) ≤ scalar12773.upperTail ∧
    exp (-((12773:ℝ)*em12773)) ≤ scalar12773.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12773:ℝ)) (by norm_num [ep12773]) ?_)
      (show bp12773^8 ≤ scalar12773.upperTail by norm_num [bp12773, scalar12773])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12773, bp12773, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12773:ℝ)) (by norm_num [em12773]) ?_)
      (show bm12773^8 ≤ scalar12773.lowerTail by norm_num [bm12773, scalar12773])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12773, bm12773, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12773 :
    agent12773.root+dsL+scalar12773.worldRadius < √(1/100/aL) ∧
    2*(agent12773.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12773, agent12773, scalar12773, tp12773, tm12773, ep12773, em12773, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12773, agent12773, scalar12773, tp12773, tm12773, ep12773, em12773, dsL]

noncomputable def master12773 : MasterCertificate 12773 world12773 agent12773 :=
  master scalar12773 dsL tp12773 tm12773 ep12773 em12773
    (by norm_num [dsL]) (by norm_num [tp12773]) (by norm_num [tm12773])
    (by norm_num [ep12773]) (by norm_num [em12773])
    positive12773 negative12773 tails12773.1 tails12773.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12773.1 tailGuards12773.2

theorem preserves12773 : master12773.toScalarCertificate = scalar12773 := rfl

noncomputable def tp12774 : ℝ := (116161411 / 500000000)
noncomputable def tm12774 : ℝ := (-((1519449931 / 2500000000)))
noncomputable def ep12774 : ℝ := (12906358252519831 / 25000000000000000000)
noncomputable def em12774 : ℝ := (50284000007400757 / 100000000000000000000)
noncomputable def bp12774 : ℝ := (21926455113657658323 / 50000000000000000000)
noncomputable def bm12774 : ℝ := (44802342046130711741 / 100000000000000000000)

theorem positive12774 :
    Eplus aL (agent12774.root+dsL) scalar12774.worldRadius world12774.frame
      agent12774.frame tp12774 ≤ -ep12774 := by
  apply positive_check (eT := (28904190917981802937 / 25000000000000000000)) (y := (37914037443777984461 / 100000000000000000000)) (u := (14610281123491900373 / 10000000000000000000))
  · norm_num [world12774, agent12774, scalar12774, tp12774, tm12774, ep12774, em12774, dsL]
  · norm_num [world12774, agent12774, scalar12774, tp12774, tm12774, ep12774, em12774, dsL]
  · norm_num [world12774, agent12774, scalar12774, tp12774, tm12774, ep12774, em12774, dsL]
  · norm_num [world12774, agent12774, scalar12774, tp12774, tm12774, ep12774, em12774, dsL]
  · norm_num [world12774, agent12774, scalar12774, tp12774, tm12774, ep12774, em12774, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12774, agent12774, tp12774, tm12774, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12774, agent12774, scalar12774, tp12774, tm12774, ep12774, em12774, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12774, agent12774, tp12774, tm12774, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12774, agent12774, scalar12774, tp12774, tm12774, ep12774, em12774, dsL]

theorem negative12774 :
    Eminus aL (agent12774.root+dsL) scalar12774.worldRadius world12774.frame
      agent12774.frame tm12774 ≤ -em12774 := by
  apply negative_check (lo := (8551478563609454399 / 12500000000000000000)) (hi := (68411828508875635193 / 100000000000000000000))
    (y := (-((35839302252809671719 / 50000000000000000000)))) (u := (9766383448602036247 / 20000000000000000000))
  · norm_num [world12774, agent12774, scalar12774, tp12774, tm12774, ep12774, em12774, dsL]
  · norm_num [world12774, agent12774, scalar12774, tp12774, tm12774, ep12774, em12774, dsL]
  · norm_num [world12774, agent12774, scalar12774, tp12774, tm12774, ep12774, em12774, dsL]
  · norm_num [world12774, agent12774, scalar12774, tp12774, tm12774, ep12774, em12774, dsL]
  · norm_num [world12774, agent12774, scalar12774, tp12774, tm12774, ep12774, em12774, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12774, agent12774, tp12774, tm12774, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12774, agent12774, tp12774, tm12774, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12774, agent12774, scalar12774, tp12774, tm12774, ep12774, em12774, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12774, agent12774, tp12774, tm12774, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12774, agent12774, scalar12774, tp12774, tm12774, ep12774, em12774, dsL]

theorem tails12774 :
    exp (-((12774:ℝ)*ep12774)) ≤ scalar12774.upperTail ∧
    exp (-((12774:ℝ)*em12774)) ≤ scalar12774.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12774:ℝ)) (by norm_num [ep12774]) ?_)
      (show bp12774^8 ≤ scalar12774.upperTail by norm_num [bp12774, scalar12774])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12774, bp12774, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12774:ℝ)) (by norm_num [em12774]) ?_)
      (show bm12774^8 ≤ scalar12774.lowerTail by norm_num [bm12774, scalar12774])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12774, bm12774, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12774 :
    agent12774.root+dsL+scalar12774.worldRadius < √(1/100/aL) ∧
    2*(agent12774.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12774, agent12774, scalar12774, tp12774, tm12774, ep12774, em12774, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12774, agent12774, scalar12774, tp12774, tm12774, ep12774, em12774, dsL]

noncomputable def master12774 : MasterCertificate 12774 world12774 agent12774 :=
  master scalar12774 dsL tp12774 tm12774 ep12774 em12774
    (by norm_num [dsL]) (by norm_num [tp12774]) (by norm_num [tm12774])
    (by norm_num [ep12774]) (by norm_num [em12774])
    positive12774 negative12774 tails12774.1 tails12774.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12774.1 tailGuards12774.2

theorem preserves12774 : master12774.toScalarCertificate = scalar12774 := rfl

end BstLean.Part268
