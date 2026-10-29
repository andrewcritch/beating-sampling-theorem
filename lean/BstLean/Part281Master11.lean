import BstLean.Part261Checker
import BstLean.Part281Scalar11
namespace BstLean.Part281
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12134 : ℝ := (94857147 / 400000000)
noncomputable def tm12134 : ℝ := (-((6135665787 / 10000000000)))
noncomputable def ep12134 : ℝ := (2727637105566659 / 5000000000000000000)
noncomputable def em12134 : ℝ := (52601903443222181 / 100000000000000000000)
noncomputable def bp12134 : ℝ := (21858596779634661537 / 50000000000000000000)
noncomputable def bm12134 : ℝ := (9006016942098980903 / 20000000000000000000)

theorem positive12134 :
    Eplus aL (agent12134.root+dsL) scalar12134.worldRadius world12134.frame
      agent12134.frame tp12134 ≤ -ep12134 := by
  apply positive_check (eT := (58109703413890805273 / 50000000000000000000)) (y := (39617188881347578149 / 100000000000000000000)) (u := (148612474381719362723 / 100000000000000000000))
  · norm_num [world12134, agent12134, scalar12134, tp12134, tm12134, ep12134, em12134, dsL]
  · norm_num [world12134, agent12134, scalar12134, tp12134, tm12134, ep12134, em12134, dsL]
  · norm_num [world12134, agent12134, scalar12134, tp12134, tm12134, ep12134, em12134, dsL]
  · norm_num [world12134, agent12134, scalar12134, tp12134, tm12134, ep12134, em12134, dsL]
  · norm_num [world12134, agent12134, scalar12134, tp12134, tm12134, ep12134, em12134, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12134, agent12134, tp12134, tm12134, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12134, agent12134, scalar12134, tp12134, tm12134, ep12134, em12134, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12134, agent12134, tp12134, tm12134, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12134, agent12134, scalar12134, tp12134, tm12134, ep12134, em12134, dsL]

theorem negative12134 :
    Eminus aL (agent12134.root+dsL) scalar12134.worldRadius world12134.frame
      agent12134.frame tm12134 ≤ -em12134 := by
  apply negative_check (lo := (67780170190092643547 / 100000000000000000000)) (hi := (16945042547523160887 / 25000000000000000000))
    (y := (-((14661978555846946031 / 20000000000000000000)))) (u := (24020895025509411841 / 50000000000000000000))
  · norm_num [world12134, agent12134, scalar12134, tp12134, tm12134, ep12134, em12134, dsL]
  · norm_num [world12134, agent12134, scalar12134, tp12134, tm12134, ep12134, em12134, dsL]
  · norm_num [world12134, agent12134, scalar12134, tp12134, tm12134, ep12134, em12134, dsL]
  · norm_num [world12134, agent12134, scalar12134, tp12134, tm12134, ep12134, em12134, dsL]
  · norm_num [world12134, agent12134, scalar12134, tp12134, tm12134, ep12134, em12134, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12134, agent12134, tp12134, tm12134, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12134, agent12134, tp12134, tm12134, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12134, agent12134, scalar12134, tp12134, tm12134, ep12134, em12134, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12134, agent12134, tp12134, tm12134, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12134, agent12134, scalar12134, tp12134, tm12134, ep12134, em12134, dsL]

theorem tails12134 :
    exp (-((12134:ℝ)*ep12134)) ≤ scalar12134.upperTail ∧
    exp (-((12134:ℝ)*em12134)) ≤ scalar12134.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12134:ℝ)) (by norm_num [ep12134]) ?_)
      (show bp12134^8 ≤ scalar12134.upperTail by norm_num [bp12134, scalar12134])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12134, bp12134, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12134:ℝ)) (by norm_num [em12134]) ?_)
      (show bm12134^8 ≤ scalar12134.lowerTail by norm_num [bm12134, scalar12134])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12134, bm12134, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12134 :
    agent12134.root+dsL+scalar12134.worldRadius < √(1/100/aL) ∧
    2*(agent12134.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12134, agent12134, scalar12134, tp12134, tm12134, ep12134, em12134, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12134, agent12134, scalar12134, tp12134, tm12134, ep12134, em12134, dsL]

noncomputable def master12134 : MasterCertificate 12134 world12134 agent12134 :=
  master scalar12134 dsL tp12134 tm12134 ep12134 em12134
    (by norm_num [dsL]) (by norm_num [tp12134]) (by norm_num [tm12134])
    (by norm_num [ep12134]) (by norm_num [em12134])
    positive12134 negative12134 tails12134.1 tails12134.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12134.1 tailGuards12134.2

theorem preserves12134 : master12134.toScalarCertificate = scalar12134 := rfl

noncomputable def tp12135 : ℝ := (474305541 / 2000000000)
noncomputable def tm12135 : ℝ := (-((3067944019 / 5000000000)))
noncomputable def ep12135 : ℝ := (27277824887578681 / 50000000000000000000)
noncomputable def em12135 : ℝ := (10520886189091963 / 20000000000000000000)
noncomputable def bp12135 : ℝ := (4371228454475174623 / 10000000000000000000)
noncomputable def bm12135 : ℝ := (22512698854288898007 / 50000000000000000000)

theorem positive12135 :
    Eplus aL (agent12135.root+dsL) scalar12135.worldRadius world12135.frame
      agent12135.frame tp12135 ≤ -ep12135 := by
  apply positive_check (eT := (29054929368897020377 / 25000000000000000000)) (y := (19808911847801777517 / 50000000000000000000)) (u := (148613417797887364869 / 100000000000000000000))
  · norm_num [world12135, agent12135, scalar12135, tp12135, tm12135, ep12135, em12135, dsL]
  · norm_num [world12135, agent12135, scalar12135, tp12135, tm12135, ep12135, em12135, dsL]
  · norm_num [world12135, agent12135, scalar12135, tp12135, tm12135, ep12135, em12135, dsL]
  · norm_num [world12135, agent12135, scalar12135, tp12135, tm12135, ep12135, em12135, dsL]
  · norm_num [world12135, agent12135, scalar12135, tp12135, tm12135, ep12135, em12135, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12135, agent12135, tp12135, tm12135, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12135, agent12135, scalar12135, tp12135, tm12135, ep12135, em12135, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12135, agent12135, tp12135, tm12135, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12135, agent12135, scalar12135, tp12135, tm12135, ep12135, em12135, dsL]

theorem negative12135 :
    Eminus aL (agent12135.root+dsL) scalar12135.worldRadius world12135.frame
      agent12135.frame tm12135 ≤ -em12135 := by
  apply negative_check (lo := (33095628605814601 / 48828125000000000)) (hi := (67779847384708302849 / 100000000000000000000))
    (y := (-((586476042039821131 / 800000000000000000)))) (u := (48041976224969545421 / 100000000000000000000))
  · norm_num [world12135, agent12135, scalar12135, tp12135, tm12135, ep12135, em12135, dsL]
  · norm_num [world12135, agent12135, scalar12135, tp12135, tm12135, ep12135, em12135, dsL]
  · norm_num [world12135, agent12135, scalar12135, tp12135, tm12135, ep12135, em12135, dsL]
  · norm_num [world12135, agent12135, scalar12135, tp12135, tm12135, ep12135, em12135, dsL]
  · norm_num [world12135, agent12135, scalar12135, tp12135, tm12135, ep12135, em12135, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12135, agent12135, tp12135, tm12135, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12135, agent12135, tp12135, tm12135, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12135, agent12135, scalar12135, tp12135, tm12135, ep12135, em12135, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12135, agent12135, tp12135, tm12135, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12135, agent12135, scalar12135, tp12135, tm12135, ep12135, em12135, dsL]

theorem tails12135 :
    exp (-((12135:ℝ)*ep12135)) ≤ scalar12135.upperTail ∧
    exp (-((12135:ℝ)*em12135)) ≤ scalar12135.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12135:ℝ)) (by norm_num [ep12135]) ?_)
      (show bp12135^8 ≤ scalar12135.upperTail by norm_num [bp12135, scalar12135])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12135, bp12135, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12135:ℝ)) (by norm_num [em12135]) ?_)
      (show bm12135^8 ≤ scalar12135.lowerTail by norm_num [bm12135, scalar12135])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12135, bm12135, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12135 :
    agent12135.root+dsL+scalar12135.worldRadius < √(1/100/aL) ∧
    2*(agent12135.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12135, agent12135, scalar12135, tp12135, tm12135, ep12135, em12135, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12135, agent12135, scalar12135, tp12135, tm12135, ep12135, em12135, dsL]

noncomputable def master12135 : MasterCertificate 12135 world12135 agent12135 :=
  master scalar12135 dsL tp12135 tm12135 ep12135 em12135
    (by norm_num [dsL]) (by norm_num [tp12135]) (by norm_num [tm12135])
    (by norm_num [ep12135]) (by norm_num [em12135])
    positive12135 negative12135 tails12135.1 tails12135.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12135.1 tailGuards12135.2

theorem preserves12135 : master12135.toScalarCertificate = scalar12135 := rfl

noncomputable def tp12136 : ℝ := (2371626749 / 10000000000)
noncomputable def tm12136 : ℝ := (-((3068055081 / 5000000000)))
noncomputable def ep12136 : ℝ := (27279278274884501 / 50000000000000000000)
noncomputable def em12136 : ℝ := (52606957647362899 / 100000000000000000000)
noncomputable def bp12136 : ℝ := (43707376353337018201 / 100000000000000000000)
noncomputable def bm12136 : ℝ := (22510355728318494977 / 50000000000000000000)

theorem positive12136 :
    Eplus aL (agent12136.root+dsL) scalar12136.worldRadius world12136.frame
      agent12136.frame tp12136 ≤ -ep12136 := by
  apply positive_check (eT := (3631875883232097783 / 3125000000000000000)) (y := (4952307396845282089 / 12500000000000000000)) (u := (18576795276023158353 / 12500000000000000000))
  · norm_num [world12136, agent12136, scalar12136, tp12136, tm12136, ep12136, em12136, dsL]
  · norm_num [world12136, agent12136, scalar12136, tp12136, tm12136, ep12136, em12136, dsL]
  · norm_num [world12136, agent12136, scalar12136, tp12136, tm12136, ep12136, em12136, dsL]
  · norm_num [world12136, agent12136, scalar12136, tp12136, tm12136, ep12136, em12136, dsL]
  · norm_num [world12136, agent12136, scalar12136, tp12136, tm12136, ep12136, em12136, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12136, agent12136, tp12136, tm12136, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12136, agent12136, scalar12136, tp12136, tm12136, ep12136, em12136, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12136, agent12136, tp12136, tm12136, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12136, agent12136, scalar12136, tp12136, tm12136, ep12136, em12136, dsL]

theorem negative12136 :
    Eminus aL (agent12136.root+dsL) scalar12136.worldRadius world12136.frame
      agent12136.frame tm12136 ≤ -em12136 := by
  apply negative_check (lo := (67779525065006169397 / 100000000000000000000)) (hi := (33889762532503084699 / 50000000000000000000))
    (y := (-((73309117672455715981 / 100000000000000000000)))) (u := (48042162427633425213 / 100000000000000000000))
  · norm_num [world12136, agent12136, scalar12136, tp12136, tm12136, ep12136, em12136, dsL]
  · norm_num [world12136, agent12136, scalar12136, tp12136, tm12136, ep12136, em12136, dsL]
  · norm_num [world12136, agent12136, scalar12136, tp12136, tm12136, ep12136, em12136, dsL]
  · norm_num [world12136, agent12136, scalar12136, tp12136, tm12136, ep12136, em12136, dsL]
  · norm_num [world12136, agent12136, scalar12136, tp12136, tm12136, ep12136, em12136, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12136, agent12136, tp12136, tm12136, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12136, agent12136, tp12136, tm12136, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12136, agent12136, scalar12136, tp12136, tm12136, ep12136, em12136, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12136, agent12136, tp12136, tm12136, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12136, agent12136, scalar12136, tp12136, tm12136, ep12136, em12136, dsL]

theorem tails12136 :
    exp (-((12136:ℝ)*ep12136)) ≤ scalar12136.upperTail ∧
    exp (-((12136:ℝ)*em12136)) ≤ scalar12136.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12136:ℝ)) (by norm_num [ep12136]) ?_)
      (show bp12136^8 ≤ scalar12136.upperTail by norm_num [bp12136, scalar12136])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12136, bp12136, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12136:ℝ)) (by norm_num [em12136]) ?_)
      (show bm12136^8 ≤ scalar12136.lowerTail by norm_num [bm12136, scalar12136])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12136, bm12136, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12136 :
    agent12136.root+dsL+scalar12136.worldRadius < √(1/100/aL) ∧
    2*(agent12136.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12136, agent12136, scalar12136, tp12136, tm12136, ep12136, em12136, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12136, agent12136, scalar12136, tp12136, tm12136, ep12136, em12136, dsL]

noncomputable def master12136 : MasterCertificate 12136 world12136 agent12136 :=
  master scalar12136 dsL tp12136 tm12136 ep12136 em12136
    (by norm_num [dsL]) (by norm_num [tp12136]) (by norm_num [tm12136])
    (by norm_num [ep12136]) (by norm_num [em12136])
    positive12136 negative12136 tails12136.1 tails12136.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12136.1 tailGuards12136.2

theorem preserves12136 : master12136.toScalarCertificate = scalar12136 := rfl

noncomputable def tp12137 : ℝ := (2371725627 / 10000000000)
noncomputable def tm12137 : ℝ := (-((3068165993 / 5000000000)))
noncomputable def ep12137 : ℝ := (2182458447821067 / 4000000000000000000)
noncomputable def em12137 : ℝ := (52609482363653911 / 100000000000000000000)
noncomputable def bp12137 : ℝ := (43702469806925796591 / 100000000000000000000)
noncomputable def bm12137 : ℝ := (22508013382079763429 / 50000000000000000000)

theorem positive12137 :
    Eplus aL (agent12137.root+dsL) scalar12137.worldRadius world12137.frame
      agent12137.frame tp12137 ≤ -ep12137 := by
  apply positive_check (eT := (116220337865378428201 / 100000000000000000000)) (y := (39619092396482350499 / 100000000000000000000)) (u := (148615303269585447353 / 100000000000000000000))
  · norm_num [world12137, agent12137, scalar12137, tp12137, tm12137, ep12137, em12137, dsL]
  · norm_num [world12137, agent12137, scalar12137, tp12137, tm12137, ep12137, em12137, dsL]
  · norm_num [world12137, agent12137, scalar12137, tp12137, tm12137, ep12137, em12137, dsL]
  · norm_num [world12137, agent12137, scalar12137, tp12137, tm12137, ep12137, em12137, dsL]
  · norm_num [world12137, agent12137, scalar12137, tp12137, tm12137, ep12137, em12137, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12137, agent12137, tp12137, tm12137, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12137, agent12137, scalar12137, tp12137, tm12137, ep12137, em12137, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12137, agent12137, tp12137, tm12137, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12137, agent12137, scalar12137, tp12137, tm12137, ep12137, em12137, dsL]

theorem negative12137 :
    Eminus aL (agent12137.root+dsL) scalar12137.worldRadius world12137.frame
      agent12137.frame tm12137 ≤ -em12137 := by
  apply negative_check (lo := (847240049677269909 / 1250000000000000000)) (hi := (67779203974181592721 / 100000000000000000000))
    (y := (-((36654364126359944907 / 50000000000000000000)))) (u := (48042349513659710799 / 100000000000000000000))
  · norm_num [world12137, agent12137, scalar12137, tp12137, tm12137, ep12137, em12137, dsL]
  · norm_num [world12137, agent12137, scalar12137, tp12137, tm12137, ep12137, em12137, dsL]
  · norm_num [world12137, agent12137, scalar12137, tp12137, tm12137, ep12137, em12137, dsL]
  · norm_num [world12137, agent12137, scalar12137, tp12137, tm12137, ep12137, em12137, dsL]
  · norm_num [world12137, agent12137, scalar12137, tp12137, tm12137, ep12137, em12137, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12137, agent12137, tp12137, tm12137, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12137, agent12137, tp12137, tm12137, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12137, agent12137, scalar12137, tp12137, tm12137, ep12137, em12137, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12137, agent12137, tp12137, tm12137, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12137, agent12137, scalar12137, tp12137, tm12137, ep12137, em12137, dsL]

theorem tails12137 :
    exp (-((12137:ℝ)*ep12137)) ≤ scalar12137.upperTail ∧
    exp (-((12137:ℝ)*em12137)) ≤ scalar12137.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12137:ℝ)) (by norm_num [ep12137]) ?_)
      (show bp12137^8 ≤ scalar12137.upperTail by norm_num [bp12137, scalar12137])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12137, bp12137, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12137:ℝ)) (by norm_num [em12137]) ?_)
      (show bm12137^8 ≤ scalar12137.lowerTail by norm_num [bm12137, scalar12137])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12137, bm12137, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12137 :
    agent12137.root+dsL+scalar12137.worldRadius < √(1/100/aL) ∧
    2*(agent12137.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12137, agent12137, scalar12137, tp12137, tm12137, ep12137, em12137, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12137, agent12137, scalar12137, tp12137, tm12137, ep12137, em12137, dsL]

noncomputable def master12137 : MasterCertificate 12137 world12137 agent12137 :=
  master scalar12137 dsL tp12137 tm12137 ep12137 em12137
    (by norm_num [dsL]) (by norm_num [tp12137]) (by norm_num [tm12137])
    (by norm_num [ep12137]) (by norm_num [em12137])
    positive12137 negative12137 tails12137.1 tails12137.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12137.1 tailGuards12137.2

theorem preserves12137 : master12137.toScalarCertificate = scalar12137 := rfl

noncomputable def tp12138 : ℝ := (2371824547 / 10000000000)
noncomputable def tm12138 : ℝ := (-((1534138449 / 2500000000)))
noncomputable def ep12138 : ℝ := (54564363873906831 / 100000000000000000000)
noncomputable def em12138 : ℝ := (52612005259900361 / 100000000000000000000)
noncomputable def bp12138 : ℝ := (21848782399188776253 / 50000000000000000000)
noncomputable def bm12138 : ℝ := (22505671759011729249 / 50000000000000000000)

theorem positive12138 :
    Eplus aL (agent12138.root+dsL) scalar12138.worldRadius world12138.frame
      agent12138.frame tp12138 ≤ -ep12138 := by
  apply positive_check (eT := (116220647813582991081 / 100000000000000000000)) (y := (39619726942845238361 / 100000000000000000000)) (u := (148616246305579036409 / 100000000000000000000))
  · norm_num [world12138, agent12138, scalar12138, tp12138, tm12138, ep12138, em12138, dsL]
  · norm_num [world12138, agent12138, scalar12138, tp12138, tm12138, ep12138, em12138, dsL]
  · norm_num [world12138, agent12138, scalar12138, tp12138, tm12138, ep12138, em12138, dsL]
  · norm_num [world12138, agent12138, scalar12138, tp12138, tm12138, ep12138, em12138, dsL]
  · norm_num [world12138, agent12138, scalar12138, tp12138, tm12138, ep12138, em12138, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12138, agent12138, tp12138, tm12138, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12138, agent12138, scalar12138, tp12138, tm12138, ep12138, em12138, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12138, agent12138, tp12138, tm12138, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12138, agent12138, scalar12138, tp12138, tm12138, ep12138, em12138, dsL]

theorem negative12138 :
    Eminus aL (agent12138.root+dsL) scalar12138.worldRadius world12138.frame
      agent12138.frame tm12138 ≤ -em12138 := by
  apply negative_check (lo := (6777888288359655683 / 10000000000000000000)) (hi := (67778882883596556831 / 100000000000000000000))
    (y := (-((36654169747331589193 / 50000000000000000000)))) (u := (4804253628252711789 / 10000000000000000000))
  · norm_num [world12138, agent12138, scalar12138, tp12138, tm12138, ep12138, em12138, dsL]
  · norm_num [world12138, agent12138, scalar12138, tp12138, tm12138, ep12138, em12138, dsL]
  · norm_num [world12138, agent12138, scalar12138, tp12138, tm12138, ep12138, em12138, dsL]
  · norm_num [world12138, agent12138, scalar12138, tp12138, tm12138, ep12138, em12138, dsL]
  · norm_num [world12138, agent12138, scalar12138, tp12138, tm12138, ep12138, em12138, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12138, agent12138, tp12138, tm12138, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12138, agent12138, tp12138, tm12138, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12138, agent12138, scalar12138, tp12138, tm12138, ep12138, em12138, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12138, agent12138, tp12138, tm12138, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12138, agent12138, scalar12138, tp12138, tm12138, ep12138, em12138, dsL]

theorem tails12138 :
    exp (-((12138:ℝ)*ep12138)) ≤ scalar12138.upperTail ∧
    exp (-((12138:ℝ)*em12138)) ≤ scalar12138.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12138:ℝ)) (by norm_num [ep12138]) ?_)
      (show bp12138^8 ≤ scalar12138.upperTail by norm_num [bp12138, scalar12138])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12138, bp12138, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12138:ℝ)) (by norm_num [em12138]) ?_)
      (show bm12138^8 ≤ scalar12138.lowerTail by norm_num [bm12138, scalar12138])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12138, bm12138, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12138 :
    agent12138.root+dsL+scalar12138.worldRadius < √(1/100/aL) ∧
    2*(agent12138.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12138, agent12138, scalar12138, tp12138, tm12138, ep12138, em12138, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12138, agent12138, scalar12138, tp12138, tm12138, ep12138, em12138, dsL]

noncomputable def master12138 : MasterCertificate 12138 world12138 agent12138 :=
  master scalar12138 dsL tp12138 tm12138 ep12138 em12138
    (by norm_num [dsL]) (by norm_num [tp12138]) (by norm_num [tm12138])
    (by norm_num [ep12138]) (by norm_num [em12138])
    positive12138 negative12138 tails12138.1 tails12138.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12138.1 tailGuards12138.2

theorem preserves12138 : master12138.toScalarCertificate = scalar12138 := rfl

noncomputable def tp12139 : ℝ := (2371923391 / 10000000000)
noncomputable def tm12139 : ℝ := (-((191774237 / 312500000)))
noncomputable def ep12139 : ℝ := (27283632803503919 / 50000000000000000000)
noncomputable def em12139 : ℝ := (52614527213912577 / 100000000000000000000)
noncomputable def bp12139 : ℝ := (43692660649988127037 / 100000000000000000000)
noncomputable def bm12139 : ℝ := (45006661118711891321 / 100000000000000000000)

theorem positive12139 :
    Eplus aL (agent12139.root+dsL) scalar12139.worldRadius world12139.frame
      agent12139.frame tp12139 ≤ -ep12139 := by
  apply positive_check (eT := (58110478619457406199 / 50000000000000000000)) (y := (3962036090789808543 / 10000000000000000000)) (u := (148617188483630003537 / 100000000000000000000))
  · norm_num [world12139, agent12139, scalar12139, tp12139, tm12139, ep12139, em12139, dsL]
  · norm_num [world12139, agent12139, scalar12139, tp12139, tm12139, ep12139, em12139, dsL]
  · norm_num [world12139, agent12139, scalar12139, tp12139, tm12139, ep12139, em12139, dsL]
  · norm_num [world12139, agent12139, scalar12139, tp12139, tm12139, ep12139, em12139, dsL]
  · norm_num [world12139, agent12139, scalar12139, tp12139, tm12139, ep12139, em12139, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12139, agent12139, tp12139, tm12139, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12139, agent12139, scalar12139, tp12139, tm12139, ep12139, em12139, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12139, agent12139, tp12139, tm12139, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12139, agent12139, scalar12139, tp12139, tm12139, ep12139, em12139, dsL]

theorem negative12139 :
    Eminus aL (agent12139.root+dsL) scalar12139.worldRadius world12139.frame
      agent12139.frame tm12139 ≤ -em12139 := by
  apply negative_check (lo := (67778561827557809521 / 100000000000000000000)) (hi := (33889280913778904761 / 50000000000000000000))
    (y := (-((733079521730143739 / 1000000000000000000)))) (u := (6005340295253892217 / 12500000000000000000))
  · norm_num [world12139, agent12139, scalar12139, tp12139, tm12139, ep12139, em12139, dsL]
  · norm_num [world12139, agent12139, scalar12139, tp12139, tm12139, ep12139, em12139, dsL]
  · norm_num [world12139, agent12139, scalar12139, tp12139, tm12139, ep12139, em12139, dsL]
  · norm_num [world12139, agent12139, scalar12139, tp12139, tm12139, ep12139, em12139, dsL]
  · norm_num [world12139, agent12139, scalar12139, tp12139, tm12139, ep12139, em12139, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12139, agent12139, tp12139, tm12139, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12139, agent12139, tp12139, tm12139, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12139, agent12139, scalar12139, tp12139, tm12139, ep12139, em12139, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12139, agent12139, tp12139, tm12139, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12139, agent12139, scalar12139, tp12139, tm12139, ep12139, em12139, dsL]

theorem tails12139 :
    exp (-((12139:ℝ)*ep12139)) ≤ scalar12139.upperTail ∧
    exp (-((12139:ℝ)*em12139)) ≤ scalar12139.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12139:ℝ)) (by norm_num [ep12139]) ?_)
      (show bp12139^8 ≤ scalar12139.upperTail by norm_num [bp12139, scalar12139])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12139, bp12139, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12139:ℝ)) (by norm_num [em12139]) ?_)
      (show bm12139^8 ≤ scalar12139.lowerTail by norm_num [bm12139, scalar12139])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12139, bm12139, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12139 :
    agent12139.root+dsL+scalar12139.worldRadius < √(1/100/aL) ∧
    2*(agent12139.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12139, agent12139, scalar12139, tp12139, tm12139, ep12139, em12139, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12139, agent12139, scalar12139, tp12139, tm12139, ep12139, em12139, dsL]

noncomputable def master12139 : MasterCertificate 12139 world12139 agent12139 :=
  master scalar12139 dsL tp12139 tm12139 ep12139 em12139
    (by norm_num [dsL]) (by norm_num [tp12139]) (by norm_num [tm12139])
    (by norm_num [ep12139]) (by norm_num [em12139])
    positive12139 negative12139 tails12139.1 tails12139.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12139.1 tailGuards12139.2

theorem preserves12139 : master12139.toScalarCertificate = scalar12139 := rfl

noncomputable def tp12140 : ℝ := (2372022357 / 10000000000)
noncomputable def tm12140 : ℝ := (-((6136997509 / 10000000000)))
noncomputable def ep12140 : ℝ := (13642542064791903 / 25000000000000000000)
noncomputable def em12140 : ℝ := (52617050579418927 / 100000000000000000000)
noncomputable def bp12140 : ℝ := (43687756125761694299 / 100000000000000000000)
noncomputable def bm12140 : ℝ := (22500988979423992269 / 50000000000000000000)

theorem positive12140 :
    Eplus aL (agent12140.root+dsL) scalar12140.worldRadius world12140.frame
      agent12140.frame tp12140 ≤ -ep12140 := by
  apply positive_check (eT := (58110633799862543139 / 50000000000000000000)) (y := (39620992832688987609 / 100000000000000000000)) (u := (148618127635454936891 / 100000000000000000000))
  · norm_num [world12140, agent12140, scalar12140, tp12140, tm12140, ep12140, em12140, dsL]
  · norm_num [world12140, agent12140, scalar12140, tp12140, tm12140, ep12140, em12140, dsL]
  · norm_num [world12140, agent12140, scalar12140, tp12140, tm12140, ep12140, em12140, dsL]
  · norm_num [world12140, agent12140, scalar12140, tp12140, tm12140, ep12140, em12140, dsL]
  · norm_num [world12140, agent12140, scalar12140, tp12140, tm12140, ep12140, em12140, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12140, agent12140, tp12140, tm12140, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12140, agent12140, scalar12140, tp12140, tm12140, ep12140, em12140, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12140, agent12140, tp12140, tm12140, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12140, agent12140, scalar12140, tp12140, tm12140, ep12140, em12140, dsL]

theorem negative12140 :
    Eminus aL (agent12140.root+dsL) scalar12140.worldRadius world12140.frame
      agent12140.frame tm12140 ≤ -em12140 := by
  apply negative_check (lo := (67778240123159418737 / 100000000000000000000)) (hi := (33889120061579709369 / 50000000000000000000))
    (y := (-((3665377871172229681 / 5000000000000000000)))) (u := (48042912010845291281 / 100000000000000000000))
  · norm_num [world12140, agent12140, scalar12140, tp12140, tm12140, ep12140, em12140, dsL]
  · norm_num [world12140, agent12140, scalar12140, tp12140, tm12140, ep12140, em12140, dsL]
  · norm_num [world12140, agent12140, scalar12140, tp12140, tm12140, ep12140, em12140, dsL]
  · norm_num [world12140, agent12140, scalar12140, tp12140, tm12140, ep12140, em12140, dsL]
  · norm_num [world12140, agent12140, scalar12140, tp12140, tm12140, ep12140, em12140, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12140, agent12140, tp12140, tm12140, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12140, agent12140, tp12140, tm12140, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12140, agent12140, scalar12140, tp12140, tm12140, ep12140, em12140, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12140, agent12140, tp12140, tm12140, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12140, agent12140, scalar12140, tp12140, tm12140, ep12140, em12140, dsL]

theorem tails12140 :
    exp (-((12140:ℝ)*ep12140)) ≤ scalar12140.upperTail ∧
    exp (-((12140:ℝ)*em12140)) ≤ scalar12140.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12140:ℝ)) (by norm_num [ep12140]) ?_)
      (show bp12140^8 ≤ scalar12140.upperTail by norm_num [bp12140, scalar12140])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12140, bp12140, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12140:ℝ)) (by norm_num [em12140]) ?_)
      (show bm12140^8 ≤ scalar12140.lowerTail by norm_num [bm12140, scalar12140])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12140, bm12140, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12140 :
    agent12140.root+dsL+scalar12140.worldRadius < √(1/100/aL) ∧
    2*(agent12140.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12140, agent12140, scalar12140, tp12140, tm12140, ep12140, em12140, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12140, agent12140, scalar12140, tp12140, tm12140, ep12140, em12140, dsL]

noncomputable def master12140 : MasterCertificate 12140 world12140 agent12140 :=
  master scalar12140 dsL tp12140 tm12140 ep12140 em12140
    (by norm_num [dsL]) (by norm_num [tp12140]) (by norm_num [tm12140])
    (by norm_num [ep12140]) (by norm_num [em12140])
    positive12140 negative12140 tails12140.1 tails12140.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12140.1 tailGuards12140.2

theorem preserves12140 : master12140.toScalarCertificate = scalar12140 := rfl

noncomputable def tp12141 : ℝ := (2372121451 / 10000000000)
noncomputable def tm12141 : ℝ := (-((1534305011 / 2500000000)))
noncomputable def ep12141 : ℝ := (27286536443055897 / 50000000000000000000)
noncomputable def em12141 : ℝ := (10523915242341843 / 20000000000000000000)
noncomputable def bp12141 : ℝ := (21841425262956557489 / 50000000000000000000)
noncomputable def bm12141 : ℝ := (8999458690892671131 / 20000000000000000000)

theorem positive12141 :
    Eplus aL (agent12141.root+dsL) scalar12141.worldRadius world12141.frame
      agent12141.frame tp12141 ≤ -ep12141 := by
  apply positive_check (eT := (116221578940129857311 / 100000000000000000000)) (y := (3962162346994897979 / 10000000000000000000)) (u := (148619064879698211407 / 100000000000000000000))
  · norm_num [world12141, agent12141, scalar12141, tp12141, tm12141, ep12141, em12141, dsL]
  · norm_num [world12141, agent12141, scalar12141, tp12141, tm12141, ep12141, em12141, dsL]
  · norm_num [world12141, agent12141, scalar12141, tp12141, tm12141, ep12141, em12141, dsL]
  · norm_num [world12141, agent12141, scalar12141, tp12141, tm12141, ep12141, em12141, dsL]
  · norm_num [world12141, agent12141, scalar12141, tp12141, tm12141, ep12141, em12141, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12141, agent12141, tp12141, tm12141, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12141, agent12141, scalar12141, tp12141, tm12141, ep12141, em12141, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12141, agent12141, tp12141, tm12141, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12141, agent12141, scalar12141, tp12141, tm12141, ep12141, em12141, dsL]

theorem negative12141 :
    Eminus aL (agent12141.root+dsL) scalar12141.worldRadius world12141.frame
      agent12141.frame tm12141 ≤ -em12141 := by
  apply negative_check (lo := (33888957869406107929 / 50000000000000000000)) (hi := (67777915738812215859 / 100000000000000000000))
    (y := (-((73307161738182637683 / 100000000000000000000)))) (u := (6005387763742953683 / 12500000000000000000))
  · norm_num [world12141, agent12141, scalar12141, tp12141, tm12141, ep12141, em12141, dsL]
  · norm_num [world12141, agent12141, scalar12141, tp12141, tm12141, ep12141, em12141, dsL]
  · norm_num [world12141, agent12141, scalar12141, tp12141, tm12141, ep12141, em12141, dsL]
  · norm_num [world12141, agent12141, scalar12141, tp12141, tm12141, ep12141, em12141, dsL]
  · norm_num [world12141, agent12141, scalar12141, tp12141, tm12141, ep12141, em12141, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12141, agent12141, tp12141, tm12141, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12141, agent12141, tp12141, tm12141, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12141, agent12141, scalar12141, tp12141, tm12141, ep12141, em12141, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12141, agent12141, tp12141, tm12141, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12141, agent12141, scalar12141, tp12141, tm12141, ep12141, em12141, dsL]

theorem tails12141 :
    exp (-((12141:ℝ)*ep12141)) ≤ scalar12141.upperTail ∧
    exp (-((12141:ℝ)*em12141)) ≤ scalar12141.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12141:ℝ)) (by norm_num [ep12141]) ?_)
      (show bp12141^8 ≤ scalar12141.upperTail by norm_num [bp12141, scalar12141])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12141, bp12141, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12141:ℝ)) (by norm_num [em12141]) ?_)
      (show bm12141^8 ≤ scalar12141.lowerTail by norm_num [bm12141, scalar12141])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12141, bm12141, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12141 :
    agent12141.root+dsL+scalar12141.worldRadius < √(1/100/aL) ∧
    2*(agent12141.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12141, agent12141, scalar12141, tp12141, tm12141, ep12141, em12141, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12141, agent12141, scalar12141, tp12141, tm12141, ep12141, em12141, dsL]

noncomputable def master12141 : MasterCertificate 12141 world12141 agent12141 :=
  master scalar12141 dsL tp12141 tm12141 ep12141 em12141
    (by norm_num [dsL]) (by norm_num [tp12141]) (by norm_num [tm12141])
    (by norm_num [ep12141]) (by norm_num [em12141])
    positive12141 negative12141 tails12141.1 tails12141.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12141.1 tailGuards12141.2

theorem preserves12141 : master12141.toScalarCertificate = scalar12141 := rfl

noncomputable def tp12142 : ℝ := (1186110229 / 5000000000)
noncomputable def tm12142 : ℝ := (-((3068721111 / 5000000000)))
noncomputable def ep12142 : ℝ := (27287987803124411 / 50000000000000000000)
noncomputable def em12142 : ℝ := (26311050008562951 / 50000000000000000000)
noncomputable def bp12142 : ℝ := (43677946423797418737 / 100000000000000000000)
noncomputable def bm12142 : ℝ := (44992610401154610733 / 100000000000000000000)

theorem positive12142 :
    Eplus aL (agent12142.root+dsL) scalar12142.worldRadius world12142.frame
      agent12142.frame tp12142 ≤ -ep12142 := by
  apply positive_check (eT := (23244377935319765751 / 20000000000000000000)) (y := (19811126715131384097 / 50000000000000000000)) (u := (148620001123774656911 / 100000000000000000000))
  · norm_num [world12142, agent12142, scalar12142, tp12142, tm12142, ep12142, em12142, dsL]
  · norm_num [world12142, agent12142, scalar12142, tp12142, tm12142, ep12142, em12142, dsL]
  · norm_num [world12142, agent12142, scalar12142, tp12142, tm12142, ep12142, em12142, dsL]
  · norm_num [world12142, agent12142, scalar12142, tp12142, tm12142, ep12142, em12142, dsL]
  · norm_num [world12142, agent12142, scalar12142, tp12142, tm12142, ep12142, em12142, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12142, agent12142, tp12142, tm12142, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12142, agent12142, scalar12142, tp12142, tm12142, ep12142, em12142, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12142, agent12142, tp12142, tm12142, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12142, agent12142, scalar12142, tp12142, tm12142, ep12142, em12142, dsL]

theorem negative12142 :
    Eminus aL (agent12142.root+dsL) scalar12142.worldRadius world12142.frame
      agent12142.frame tm12142 ≤ -em12142 := by
  apply negative_check (lo := (67777592828112702901 / 100000000000000000000)) (hi := (33888796414056351451 / 50000000000000000000))
    (y := (-((73306763955134473631 / 100000000000000000000)))) (u := (48043293217639731723 / 100000000000000000000))
  · norm_num [world12142, agent12142, scalar12142, tp12142, tm12142, ep12142, em12142, dsL]
  · norm_num [world12142, agent12142, scalar12142, tp12142, tm12142, ep12142, em12142, dsL]
  · norm_num [world12142, agent12142, scalar12142, tp12142, tm12142, ep12142, em12142, dsL]
  · norm_num [world12142, agent12142, scalar12142, tp12142, tm12142, ep12142, em12142, dsL]
  · norm_num [world12142, agent12142, scalar12142, tp12142, tm12142, ep12142, em12142, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12142, agent12142, tp12142, tm12142, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12142, agent12142, tp12142, tm12142, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12142, agent12142, scalar12142, tp12142, tm12142, ep12142, em12142, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12142, agent12142, tp12142, tm12142, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12142, agent12142, scalar12142, tp12142, tm12142, ep12142, em12142, dsL]

theorem tails12142 :
    exp (-((12142:ℝ)*ep12142)) ≤ scalar12142.upperTail ∧
    exp (-((12142:ℝ)*em12142)) ≤ scalar12142.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12142:ℝ)) (by norm_num [ep12142]) ?_)
      (show bp12142^8 ≤ scalar12142.upperTail by norm_num [bp12142, scalar12142])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12142, bp12142, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12142:ℝ)) (by norm_num [em12142]) ?_)
      (show bm12142^8 ≤ scalar12142.lowerTail by norm_num [bm12142, scalar12142])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12142, bm12142, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12142 :
    agent12142.root+dsL+scalar12142.worldRadius < √(1/100/aL) ∧
    2*(agent12142.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12142, agent12142, scalar12142, tp12142, tm12142, ep12142, em12142, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12142, agent12142, scalar12142, tp12142, tm12142, ep12142, em12142, dsL]

noncomputable def master12142 : MasterCertificate 12142 world12142 agent12142 :=
  master scalar12142 dsL tp12142 tm12142 ep12142 em12142
    (by norm_num [dsL]) (by norm_num [tp12142]) (by norm_num [tm12142])
    (by norm_num [ep12142]) (by norm_num [em12142])
    positive12142 negative12142 tails12142.1 tails12142.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12142.1 tailGuards12142.2

theorem preserves12142 : master12142.toScalarCertificate = scalar12142 := rfl

noncomputable def tp12143 : ℝ := (1186159699 / 5000000000)
noncomputable def tm12143 : ℝ := (-((6137664349 / 10000000000)))
noncomputable def ep12143 : ℝ := (3411179849743687 / 6250000000000000000)
noncomputable def em12143 : ℝ := (52624623186026059 / 100000000000000000000)
noncomputable def bp12143 : ℝ := (43673043039560804667 / 100000000000000000000)
noncomputable def bm12143 : ℝ := (11246981996507634399 / 25000000000000000000)

theorem positive12143 :
    Eplus aL (agent12143.root+dsL) scalar12143.worldRadius world12143.frame
      agent12143.frame tp12143 ≤ -ep12143 := by
  apply positive_check (eT := (116222199956426766733 / 100000000000000000000)) (y := (39622882435432273157 / 100000000000000000000)) (u := (148620935954204706571 / 100000000000000000000))
  · norm_num [world12143, agent12143, scalar12143, tp12143, tm12143, ep12143, em12143, dsL]
  · norm_num [world12143, agent12143, scalar12143, tp12143, tm12143, ep12143, em12143, dsL]
  · norm_num [world12143, agent12143, scalar12143, tp12143, tm12143, ep12143, em12143, dsL]
  · norm_num [world12143, agent12143, scalar12143, tp12143, tm12143, ep12143, em12143, dsL]
  · norm_num [world12143, agent12143, scalar12143, tp12143, tm12143, ep12143, em12143, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12143, agent12143, tp12143, tm12143, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12143, agent12143, scalar12143, tp12143, tm12143, ep12143, em12143, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12143, agent12143, tp12143, tm12143, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12143, agent12143, scalar12143, tp12143, tm12143, ep12143, em12143, dsL]

theorem negative12143 :
    Eminus aL (agent12143.root+dsL) scalar12143.worldRadius world12143.frame
      agent12143.frame tm12143 ≤ -em12143 := by
  apply negative_check (lo := (16944317519179729877 / 25000000000000000000)) (hi := (67777270076718919509 / 100000000000000000000))
    (y := (-((9163295819476704237 / 12500000000000000000)))) (u := (24021742070870026477 / 50000000000000000000))
  · norm_num [world12143, agent12143, scalar12143, tp12143, tm12143, ep12143, em12143, dsL]
  · norm_num [world12143, agent12143, scalar12143, tp12143, tm12143, ep12143, em12143, dsL]
  · norm_num [world12143, agent12143, scalar12143, tp12143, tm12143, ep12143, em12143, dsL]
  · norm_num [world12143, agent12143, scalar12143, tp12143, tm12143, ep12143, em12143, dsL]
  · norm_num [world12143, agent12143, scalar12143, tp12143, tm12143, ep12143, em12143, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12143, agent12143, tp12143, tm12143, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12143, agent12143, tp12143, tm12143, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12143, agent12143, scalar12143, tp12143, tm12143, ep12143, em12143, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12143, agent12143, tp12143, tm12143, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12143, agent12143, scalar12143, tp12143, tm12143, ep12143, em12143, dsL]

theorem tails12143 :
    exp (-((12143:ℝ)*ep12143)) ≤ scalar12143.upperTail ∧
    exp (-((12143:ℝ)*em12143)) ≤ scalar12143.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12143:ℝ)) (by norm_num [ep12143]) ?_)
      (show bp12143^8 ≤ scalar12143.upperTail by norm_num [bp12143, scalar12143])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12143, bp12143, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12143:ℝ)) (by norm_num [em12143]) ?_)
      (show bm12143^8 ≤ scalar12143.lowerTail by norm_num [bm12143, scalar12143])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12143, bm12143, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12143 :
    agent12143.root+dsL+scalar12143.worldRadius < √(1/100/aL) ∧
    2*(agent12143.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12143, agent12143, scalar12143, tp12143, tm12143, ep12143, em12143, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12143, agent12143, scalar12143, tp12143, tm12143, ep12143, em12143, dsL]

noncomputable def master12143 : MasterCertificate 12143 world12143 agent12143 :=
  master scalar12143 dsL tp12143 tm12143 ep12143 em12143
    (by norm_num [dsL]) (by norm_num [tp12143]) (by norm_num [tm12143])
    (by norm_num [ep12143]) (by norm_num [em12143])
    positive12143 negative12143 tails12143.1 tails12143.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12143.1 tailGuards12143.2

theorem preserves12143 : master12143.toScalarCertificate = scalar12143 := rfl

noncomputable def tp12144 : ℝ := (296552291 / 1250000000)
noncomputable def tm12144 : ℝ := (-((6137886471 / 10000000000)))
noncomputable def ep12144 : ℝ := (27290888416216923 / 50000000000000000000)
noncomputable def em12144 : ℝ := (52627143777086101 / 100000000000000000000)
noncomputable def bp12144 : ℝ := (43668141713969503137 / 100000000000000000000)
noncomputable def bm12144 : ℝ := (22491623767362570379 / 50000000000000000000)

theorem positive12144 :
    Eplus aL (agent12144.root+dsL) scalar12144.worldRadius world12144.frame
      agent12144.frame tp12144 ≤ -ep12144 := by
  apply positive_check (eT := (14527813774927792983 / 12500000000000000000)) (y := (495293902484698051 / 1250000000000000000)) (u := (29724374383465478281 / 20000000000000000000))
  · norm_num [world12144, agent12144, scalar12144, tp12144, tm12144, ep12144, em12144, dsL]
  · norm_num [world12144, agent12144, scalar12144, tp12144, tm12144, ep12144, em12144, dsL]
  · norm_num [world12144, agent12144, scalar12144, tp12144, tm12144, ep12144, em12144, dsL]
  · norm_num [world12144, agent12144, scalar12144, tp12144, tm12144, ep12144, em12144, dsL]
  · norm_num [world12144, agent12144, scalar12144, tp12144, tm12144, ep12144, em12144, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12144, agent12144, tp12144, tm12144, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12144, agent12144, scalar12144, tp12144, tm12144, ep12144, em12144, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12144, agent12144, tp12144, tm12144, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12144, agent12144, scalar12144, tp12144, tm12144, ep12144, em12144, dsL]

theorem negative12144 :
    Eminus aL (agent12144.root+dsL) scalar12144.worldRadius world12144.frame
      agent12144.frame tm12144 ≤ -em12144 := by
  apply negative_check (lo := (67776947287076675257 / 100000000000000000000)) (hi := (33888473643538337629 / 50000000000000000000))
    (y := (-((36652985182077507371 / 50000000000000000000)))) (u := (9608734897278759423 / 20000000000000000000))
  · norm_num [world12144, agent12144, scalar12144, tp12144, tm12144, ep12144, em12144, dsL]
  · norm_num [world12144, agent12144, scalar12144, tp12144, tm12144, ep12144, em12144, dsL]
  · norm_num [world12144, agent12144, scalar12144, tp12144, tm12144, ep12144, em12144, dsL]
  · norm_num [world12144, agent12144, scalar12144, tp12144, tm12144, ep12144, em12144, dsL]
  · norm_num [world12144, agent12144, scalar12144, tp12144, tm12144, ep12144, em12144, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12144, agent12144, tp12144, tm12144, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12144, agent12144, tp12144, tm12144, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12144, agent12144, scalar12144, tp12144, tm12144, ep12144, em12144, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12144, agent12144, tp12144, tm12144, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12144, agent12144, scalar12144, tp12144, tm12144, ep12144, em12144, dsL]

theorem tails12144 :
    exp (-((12144:ℝ)*ep12144)) ≤ scalar12144.upperTail ∧
    exp (-((12144:ℝ)*em12144)) ≤ scalar12144.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12144:ℝ)) (by norm_num [ep12144]) ?_)
      (show bp12144^8 ≤ scalar12144.upperTail by norm_num [bp12144, scalar12144])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12144, bp12144, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12144:ℝ)) (by norm_num [em12144]) ?_)
      (show bm12144^8 ≤ scalar12144.lowerTail by norm_num [bm12144, scalar12144])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12144, bm12144, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12144 :
    agent12144.root+dsL+scalar12144.worldRadius < √(1/100/aL) ∧
    2*(agent12144.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12144, agent12144, scalar12144, tp12144, tm12144, ep12144, em12144, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12144, agent12144, scalar12144, tp12144, tm12144, ep12144, em12144, dsL]

noncomputable def master12144 : MasterCertificate 12144 world12144 agent12144 :=
  master scalar12144 dsL tp12144 tm12144 ep12144 em12144
    (by norm_num [dsL]) (by norm_num [tp12144]) (by norm_num [tm12144])
    (by norm_num [ep12144]) (by norm_num [em12144])
    positive12144 negative12144 tails12144.1 tails12144.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12144.1 tailGuards12144.2

theorem preserves12144 : master12144.toScalarCertificate = scalar12144 := rfl

noncomputable def tp12145 : ℝ := (2372517161 / 10000000000)
noncomputable def tm12145 : ℝ := (-((3069054077 / 5000000000)))
noncomputable def ep12145 : ℝ := (54584675398308371 / 100000000000000000000)
noncomputable def em12145 : ℝ := (10525932744801431 / 20000000000000000000)
noncomputable def bp12145 : ℝ := (10915810266630805529 / 25000000000000000000)
noncomputable def bm12145 : ℝ := (2248928386338540221 / 5000000000000000000)

theorem positive12145 :
    Eplus aL (agent12145.root+dsL) scalar12145.worldRadius world12145.frame
      agent12145.frame tp12145 ≤ -ep12145 := by
  apply positive_check (eT := (116222819764872424729 / 100000000000000000000)) (y := (39624140787672010131 / 100000000000000000000)) (u := (37155701535211936859 / 25000000000000000000))
  · norm_num [world12145, agent12145, scalar12145, tp12145, tm12145, ep12145, em12145, dsL]
  · norm_num [world12145, agent12145, scalar12145, tp12145, tm12145, ep12145, em12145, dsL]
  · norm_num [world12145, agent12145, scalar12145, tp12145, tm12145, ep12145, em12145, dsL]
  · norm_num [world12145, agent12145, scalar12145, tp12145, tm12145, ep12145, em12145, dsL]
  · norm_num [world12145, agent12145, scalar12145, tp12145, tm12145, ep12145, em12145, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12145, agent12145, tp12145, tm12145, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12145, agent12145, scalar12145, tp12145, tm12145, ep12145, em12145, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12145, agent12145, tp12145, tm12145, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12145, agent12145, scalar12145, tp12145, tm12145, ep12145, em12145, dsL]

theorem negative12145 :
    Eminus aL (agent12145.root+dsL) scalar12145.worldRadius world12145.frame
      agent12145.frame tm12145 ≤ -em12145 := by
  apply negative_check (lo := (67776626323113818047 / 100000000000000000000)) (hi := (1059009786298653407 / 1562500000000000000))
    (y := (-((36652785679650384307 / 50000000000000000000)))) (u := (480438661833695959 / 1000000000000000000))
  · norm_num [world12145, agent12145, scalar12145, tp12145, tm12145, ep12145, em12145, dsL]
  · norm_num [world12145, agent12145, scalar12145, tp12145, tm12145, ep12145, em12145, dsL]
  · norm_num [world12145, agent12145, scalar12145, tp12145, tm12145, ep12145, em12145, dsL]
  · norm_num [world12145, agent12145, scalar12145, tp12145, tm12145, ep12145, em12145, dsL]
  · norm_num [world12145, agent12145, scalar12145, tp12145, tm12145, ep12145, em12145, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12145, agent12145, tp12145, tm12145, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12145, agent12145, tp12145, tm12145, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12145, agent12145, scalar12145, tp12145, tm12145, ep12145, em12145, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12145, agent12145, tp12145, tm12145, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12145, agent12145, scalar12145, tp12145, tm12145, ep12145, em12145, dsL]

theorem tails12145 :
    exp (-((12145:ℝ)*ep12145)) ≤ scalar12145.upperTail ∧
    exp (-((12145:ℝ)*em12145)) ≤ scalar12145.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12145:ℝ)) (by norm_num [ep12145]) ?_)
      (show bp12145^8 ≤ scalar12145.upperTail by norm_num [bp12145, scalar12145])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12145, bp12145, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12145:ℝ)) (by norm_num [em12145]) ?_)
      (show bm12145^8 ≤ scalar12145.lowerTail by norm_num [bm12145, scalar12145])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12145, bm12145, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12145 :
    agent12145.root+dsL+scalar12145.worldRadius < √(1/100/aL) ∧
    2*(agent12145.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12145, agent12145, scalar12145, tp12145, tm12145, ep12145, em12145, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12145, agent12145, scalar12145, tp12145, tm12145, ep12145, em12145, dsL]

noncomputable def master12145 : MasterCertificate 12145 world12145 agent12145 :=
  master scalar12145 dsL tp12145 tm12145 ep12145 em12145
    (by norm_num [dsL]) (by norm_num [tp12145]) (by norm_num [tm12145])
    (by norm_num [ep12145]) (by norm_num [em12145])
    positive12145 negative12145 tails12145.1 tails12145.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12145.1 tailGuards12145.2

theorem preserves12145 : master12145.toScalarCertificate = scalar12145 := rfl

noncomputable def tp12146 : ℝ := (593153997 / 2500000000)
noncomputable def tm12146 : ℝ := (-((3069164957 / 5000000000)))
noncomputable def ep12146 : ℝ := (13646892812963137 / 25000000000000000000)
noncomputable def em12146 : ℝ := (52632181120284481 / 100000000000000000000)
noncomputable def bp12146 : ℝ := (2728646403158320397 / 6250000000000000000)
noncomputable def bm12146 : ℝ := (44973889863968767927 / 100000000000000000000)

theorem positive12146 :
    Eplus aL (agent12146.root+dsL) scalar12146.worldRadius world12146.frame
      agent12146.frame tp12146 ≤ -ep12146 := by
  apply positive_check (eT := (23244625864600641231 / 20000000000000000000)) (y := (19812385049543193739 / 50000000000000000000)) (u := (74311870722037070801 / 50000000000000000000))
  · norm_num [world12146, agent12146, scalar12146, tp12146, tm12146, ep12146, em12146, dsL]
  · norm_num [world12146, agent12146, scalar12146, tp12146, tm12146, ep12146, em12146, dsL]
  · norm_num [world12146, agent12146, scalar12146, tp12146, tm12146, ep12146, em12146, dsL]
  · norm_num [world12146, agent12146, scalar12146, tp12146, tm12146, ep12146, em12146, dsL]
  · norm_num [world12146, agent12146, scalar12146, tp12146, tm12146, ep12146, em12146, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12146, agent12146, tp12146, tm12146, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12146, agent12146, scalar12146, tp12146, tm12146, ep12146, em12146, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12146, agent12146, tp12146, tm12146, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12146, agent12146, scalar12146, tp12146, tm12146, ep12146, em12146, dsL]

theorem negative12146 :
    Eminus aL (agent12146.root+dsL) scalar12146.worldRadius world12146.frame
      agent12146.frame tm12146 ≤ -em12146 := by
  apply negative_check (lo := (67776304968607387331 / 100000000000000000000)) (hi := (16944076242151846833 / 25000000000000000000))
    (y := (-((36652586970413313969 / 50000000000000000000)))) (u := (48044057118948906417 / 100000000000000000000))
  · norm_num [world12146, agent12146, scalar12146, tp12146, tm12146, ep12146, em12146, dsL]
  · norm_num [world12146, agent12146, scalar12146, tp12146, tm12146, ep12146, em12146, dsL]
  · norm_num [world12146, agent12146, scalar12146, tp12146, tm12146, ep12146, em12146, dsL]
  · norm_num [world12146, agent12146, scalar12146, tp12146, tm12146, ep12146, em12146, dsL]
  · norm_num [world12146, agent12146, scalar12146, tp12146, tm12146, ep12146, em12146, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12146, agent12146, tp12146, tm12146, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12146, agent12146, tp12146, tm12146, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12146, agent12146, scalar12146, tp12146, tm12146, ep12146, em12146, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12146, agent12146, tp12146, tm12146, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12146, agent12146, scalar12146, tp12146, tm12146, ep12146, em12146, dsL]

theorem tails12146 :
    exp (-((12146:ℝ)*ep12146)) ≤ scalar12146.upperTail ∧
    exp (-((12146:ℝ)*em12146)) ≤ scalar12146.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12146:ℝ)) (by norm_num [ep12146]) ?_)
      (show bp12146^8 ≤ scalar12146.upperTail by norm_num [bp12146, scalar12146])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12146, bp12146, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12146:ℝ)) (by norm_num [em12146]) ?_)
      (show bm12146^8 ≤ scalar12146.lowerTail by norm_num [bm12146, scalar12146])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12146, bm12146, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12146 :
    agent12146.root+dsL+scalar12146.worldRadius < √(1/100/aL) ∧
    2*(agent12146.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12146, agent12146, scalar12146, tp12146, tm12146, ep12146, em12146, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12146, agent12146, scalar12146, tp12146, tm12146, ep12146, em12146, dsL]

noncomputable def master12146 : MasterCertificate 12146 world12146 agent12146 :=
  master scalar12146 dsL tp12146 tm12146 ep12146 em12146
    (by norm_num [dsL]) (by norm_num [tp12146]) (by norm_num [tm12146])
    (by norm_num [ep12146]) (by norm_num [em12146])
    positive12146 negative12146 tails12146.1 tails12146.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12146.1 tailGuards12146.2

theorem preserves12146 : master12146.toScalarCertificate = scalar12146 := rfl

noncomputable def tp12147 : ℝ := (148294673 / 625000000)
noncomputable def tm12147 : ℝ := (-((6138551563 / 10000000000)))
noncomputable def ep12147 : ℝ := (27295233112026473 / 50000000000000000000)
noncomputable def em12147 : ℝ := (52634697723851447 / 100000000000000000000)
noncomputable def bp12147 : ℝ := (43653444652262868927 / 100000000000000000000)
noncomputable def bm12147 : ℝ := (2248460637296216747 / 5000000000000000000)

theorem positive12147 :
    Eplus aL (agent12147.root+dsL) scalar12147.worldRadius world12147.frame
      agent12147.frame tp12147 ≤ -ep12147 := by
  apply positive_check (eT := (116223438571804973451 / 100000000000000000000)) (y := (39625398973633395357 / 100000000000000000000)) (u := (74312338051946904979 / 50000000000000000000))
  · norm_num [world12147, agent12147, scalar12147, tp12147, tm12147, ep12147, em12147, dsL]
  · norm_num [world12147, agent12147, scalar12147, tp12147, tm12147, ep12147, em12147, dsL]
  · norm_num [world12147, agent12147, scalar12147, tp12147, tm12147, ep12147, em12147, dsL]
  · norm_num [world12147, agent12147, scalar12147, tp12147, tm12147, ep12147, em12147, dsL]
  · norm_num [world12147, agent12147, scalar12147, tp12147, tm12147, ep12147, em12147, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12147, agent12147, tp12147, tm12147, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12147, agent12147, scalar12147, tp12147, tm12147, ep12147, em12147, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12147, agent12147, tp12147, tm12147, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12147, agent12147, scalar12147, tp12147, tm12147, ep12147, em12147, dsL]

theorem negative12147 :
    Eminus aL (agent12147.root+dsL) scalar12147.worldRadius world12147.frame
      agent12147.frame tm12147 ≤ -em12147 := by
  apply negative_check (lo := (1694399600776870751 / 2500000000000000000)) (hi := (67775984031074830041 / 100000000000000000000))
    (y := (-((36652388306468297821 / 50000000000000000000)))) (u := (48044248011766577999 / 100000000000000000000))
  · norm_num [world12147, agent12147, scalar12147, tp12147, tm12147, ep12147, em12147, dsL]
  · norm_num [world12147, agent12147, scalar12147, tp12147, tm12147, ep12147, em12147, dsL]
  · norm_num [world12147, agent12147, scalar12147, tp12147, tm12147, ep12147, em12147, dsL]
  · norm_num [world12147, agent12147, scalar12147, tp12147, tm12147, ep12147, em12147, dsL]
  · norm_num [world12147, agent12147, scalar12147, tp12147, tm12147, ep12147, em12147, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12147, agent12147, tp12147, tm12147, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12147, agent12147, tp12147, tm12147, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12147, agent12147, scalar12147, tp12147, tm12147, ep12147, em12147, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12147, agent12147, tp12147, tm12147, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12147, agent12147, scalar12147, tp12147, tm12147, ep12147, em12147, dsL]

theorem tails12147 :
    exp (-((12147:ℝ)*ep12147)) ≤ scalar12147.upperTail ∧
    exp (-((12147:ℝ)*em12147)) ≤ scalar12147.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12147:ℝ)) (by norm_num [ep12147]) ?_)
      (show bp12147^8 ≤ scalar12147.upperTail by norm_num [bp12147, scalar12147])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12147, bp12147, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12147:ℝ)) (by norm_num [em12147]) ?_)
      (show bm12147^8 ≤ scalar12147.lowerTail by norm_num [bm12147, scalar12147])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12147, bm12147, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12147 :
    agent12147.root+dsL+scalar12147.worldRadius < √(1/100/aL) ∧
    2*(agent12147.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12147, agent12147, scalar12147, tp12147, tm12147, ep12147, em12147, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12147, agent12147, scalar12147, tp12147, tm12147, ep12147, em12147, dsL]

noncomputable def master12147 : MasterCertificate 12147 world12147 agent12147 :=
  master scalar12147 dsL tp12147 tm12147 ep12147 em12147
    (by norm_num [dsL]) (by norm_num [tp12147]) (by norm_num [tm12147])
    (by norm_num [ep12147]) (by norm_num [em12147])
    positive12147 negative12147 tails12147.1 tails12147.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12147.1 tailGuards12147.2

theorem preserves12147 : master12147.toScalarCertificate = scalar12147 := rfl

noncomputable def tp12148 : ℝ := (94912537 / 400000000)
noncomputable def tm12148 : ℝ := (-((3069386553 / 5000000000)))
noncomputable def ep12148 : ℝ := (54593359895435177 / 100000000000000000000)
noncomputable def em12148 : ℝ := (1052744261715319 / 2000000000000000000)
noncomputable def bp12148 : ℝ := (2182427397486688731 / 5000000000000000000)
noncomputable def bm12148 : ℝ := (702570885612056287 / 1562500000000000000)

theorem positive12148 :
    Eplus aL (agent12148.root+dsL) scalar12148.worldRadius world12148.frame
      agent12148.frame tp12148 ≤ -ep12148 := by
  apply positive_check (eT := (58111873475842146631 / 50000000000000000000)) (y := (2476626651051294047 / 6250000000000000000)) (u := (148625608642224255547 / 100000000000000000000))
  · norm_num [world12148, agent12148, scalar12148, tp12148, tm12148, ep12148, em12148, dsL]
  · norm_num [world12148, agent12148, scalar12148, tp12148, tm12148, ep12148, em12148, dsL]
  · norm_num [world12148, agent12148, scalar12148, tp12148, tm12148, ep12148, em12148, dsL]
  · norm_num [world12148, agent12148, scalar12148, tp12148, tm12148, ep12148, em12148, dsL]
  · norm_num [world12148, agent12148, scalar12148, tp12148, tm12148, ep12148, em12148, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12148, agent12148, tp12148, tm12148, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12148, agent12148, scalar12148, tp12148, tm12148, ep12148, em12148, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12148, agent12148, tp12148, tm12148, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12148, agent12148, scalar12148, tp12148, tm12148, ep12148, em12148, dsL]

theorem negative12148 :
    Eminus aL (agent12148.root+dsL) scalar12148.worldRadius world12148.frame
      agent12148.frame tm12148 ≤ -em12148 := by
  apply negative_check (lo := (33887831744454551103 / 50000000000000000000)) (hi := (67775663488909102207 / 100000000000000000000))
    (y := (-((458152374313364767 / 625000000000000000)))) (u := (48044438614629762501 / 100000000000000000000))
  · norm_num [world12148, agent12148, scalar12148, tp12148, tm12148, ep12148, em12148, dsL]
  · norm_num [world12148, agent12148, scalar12148, tp12148, tm12148, ep12148, em12148, dsL]
  · norm_num [world12148, agent12148, scalar12148, tp12148, tm12148, ep12148, em12148, dsL]
  · norm_num [world12148, agent12148, scalar12148, tp12148, tm12148, ep12148, em12148, dsL]
  · norm_num [world12148, agent12148, scalar12148, tp12148, tm12148, ep12148, em12148, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12148, agent12148, tp12148, tm12148, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12148, agent12148, tp12148, tm12148, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12148, agent12148, scalar12148, tp12148, tm12148, ep12148, em12148, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12148, agent12148, tp12148, tm12148, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12148, agent12148, scalar12148, tp12148, tm12148, ep12148, em12148, dsL]

theorem tails12148 :
    exp (-((12148:ℝ)*ep12148)) ≤ scalar12148.upperTail ∧
    exp (-((12148:ℝ)*em12148)) ≤ scalar12148.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12148:ℝ)) (by norm_num [ep12148]) ?_)
      (show bp12148^8 ≤ scalar12148.upperTail by norm_num [bp12148, scalar12148])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12148, bp12148, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12148:ℝ)) (by norm_num [em12148]) ?_)
      (show bm12148^8 ≤ scalar12148.lowerTail by norm_num [bm12148, scalar12148])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12148, bm12148, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12148 :
    agent12148.root+dsL+scalar12148.worldRadius < √(1/100/aL) ∧
    2*(agent12148.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12148, agent12148, scalar12148, tp12148, tm12148, ep12148, em12148, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12148, agent12148, scalar12148, tp12148, tm12148, ep12148, em12148, dsL]

noncomputable def master12148 : MasterCertificate 12148 world12148 agent12148 :=
  master scalar12148 dsL tp12148 tm12148 ep12148 em12148
    (by norm_num [dsL]) (by norm_num [tp12148]) (by norm_num [tm12148])
    (by norm_num [ep12148]) (by norm_num [em12148])
    positive12148 negative12148 tails12148.1 tails12148.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12148.1 tailGuards12148.2

theorem preserves12148 : master12148.toScalarCertificate = scalar12148 := rfl

noncomputable def tp12149 : ℝ := (474582421 / 2000000000)
noncomputable def tm12149 : ℝ := (-((767374309 / 1250000000)))
noncomputable def ep12149 : ℝ := (54596251002016523 / 100000000000000000000)
noncomputable def em12149 : ℝ := (52639726050958041 / 100000000000000000000)
noncomputable def bp12149 : ℝ := (8728730636132011381 / 20000000000000000000)
noncomputable def bm12149 : ℝ := (44959862452342189019 / 100000000000000000000)

theorem positive12149 :
    Eplus aL (agent12149.root+dsL) scalar12149.worldRadius world12149.frame
      agent12149.frame tp12149 ≤ -ep12149 := by
  apply positive_check (eT := (58112027768902228099 / 50000000000000000000)) (y := (3962665494313140369 / 10000000000000000000)) (u := (37156635699053676773 / 25000000000000000000))
  · norm_num [world12149, agent12149, scalar12149, tp12149, tm12149, ep12149, em12149, dsL]
  · norm_num [world12149, agent12149, scalar12149, tp12149, tm12149, ep12149, em12149, dsL]
  · norm_num [world12149, agent12149, scalar12149, tp12149, tm12149, ep12149, em12149, dsL]
  · norm_num [world12149, agent12149, scalar12149, tp12149, tm12149, ep12149, em12149, dsL]
  · norm_num [world12149, agent12149, scalar12149, tp12149, tm12149, ep12149, em12149, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12149, agent12149, tp12149, tm12149, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12149, agent12149, scalar12149, tp12149, tm12149, ep12149, em12149, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12149, agent12149, tp12149, tm12149, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12149, agent12149, scalar12149, tp12149, tm12149, ep12149, em12149, dsL]

theorem negative12149 :
    Eminus aL (agent12149.root+dsL) scalar12149.worldRadius world12149.frame
      agent12149.frame tm12149 ≤ -em12149 := by
  apply negative_check (lo := (33887671823519479053 / 50000000000000000000)) (hi := (67775343647038958107 / 100000000000000000000))
    (y := (-((73303981974175269131 / 100000000000000000000)))) (u := (9608925958300150041 / 20000000000000000000))
  · norm_num [world12149, agent12149, scalar12149, tp12149, tm12149, ep12149, em12149, dsL]
  · norm_num [world12149, agent12149, scalar12149, tp12149, tm12149, ep12149, em12149, dsL]
  · norm_num [world12149, agent12149, scalar12149, tp12149, tm12149, ep12149, em12149, dsL]
  · norm_num [world12149, agent12149, scalar12149, tp12149, tm12149, ep12149, em12149, dsL]
  · norm_num [world12149, agent12149, scalar12149, tp12149, tm12149, ep12149, em12149, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12149, agent12149, tp12149, tm12149, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12149, agent12149, tp12149, tm12149, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12149, agent12149, scalar12149, tp12149, tm12149, ep12149, em12149, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12149, agent12149, tp12149, tm12149, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12149, agent12149, scalar12149, tp12149, tm12149, ep12149, em12149, dsL]

theorem tails12149 :
    exp (-((12149:ℝ)*ep12149)) ≤ scalar12149.upperTail ∧
    exp (-((12149:ℝ)*em12149)) ≤ scalar12149.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12149:ℝ)) (by norm_num [ep12149]) ?_)
      (show bp12149^8 ≤ scalar12149.upperTail by norm_num [bp12149, scalar12149])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12149, bp12149, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12149:ℝ)) (by norm_num [em12149]) ?_)
      (show bm12149^8 ≤ scalar12149.lowerTail by norm_num [bm12149, scalar12149])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12149, bm12149, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12149 :
    agent12149.root+dsL+scalar12149.worldRadius < √(1/100/aL) ∧
    2*(agent12149.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12149, agent12149, scalar12149, tp12149, tm12149, ep12149, em12149, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12149, agent12149, scalar12149, tp12149, tm12149, ep12149, em12149, dsL]

noncomputable def master12149 : MasterCertificate 12149 world12149 agent12149 :=
  master scalar12149 dsL tp12149 tm12149 ep12149 em12149
    (by norm_num [dsL]) (by norm_num [tp12149]) (by norm_num [tm12149])
    (by norm_num [ep12149]) (by norm_num [em12149])
    positive12149 negative12149 tails12149.1 tails12149.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12149.1 tailGuards12149.2

theorem preserves12149 : master12149.toScalarCertificate = scalar12149 := rfl

noncomputable def tp12150 : ℝ := (2373010721 / 10000000000)
noncomputable def tm12150 : ℝ := (-((6139215717 / 10000000000)))
noncomputable def ep12150 : ℝ := (6824892635118191 / 12500000000000000000)
noncomputable def em12150 : ℝ := (6580279758877209 / 12500000000000000000)
noncomputable def bp12150 : ℝ := (43638759326167949259 / 100000000000000000000)
noncomputable def bm12150 : ℝ := (11238797268571074997 / 25000000000000000000)

theorem positive12150 :
    Eplus aL (agent12150.root+dsL) scalar12150.worldRadius world12150.frame
      agent12150.frame tp12150 ≤ -ep12150 := by
  apply positive_check (eT := (116224363689477353451 / 100000000000000000000)) (y := (19813641442818043127 / 50000000000000000000)) (u := (148627476088380430779 / 100000000000000000000))
  · norm_num [world12150, agent12150, scalar12150, tp12150, tm12150, ep12150, em12150, dsL]
  · norm_num [world12150, agent12150, scalar12150, tp12150, tm12150, ep12150, em12150, dsL]
  · norm_num [world12150, agent12150, scalar12150, tp12150, tm12150, ep12150, em12150, dsL]
  · norm_num [world12150, agent12150, scalar12150, tp12150, tm12150, ep12150, em12150, dsL]
  · norm_num [world12150, agent12150, scalar12150, tp12150, tm12150, ep12150, em12150, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12150, agent12150, tp12150, tm12150, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12150, agent12150, scalar12150, tp12150, tm12150, ep12150, em12150, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12150, agent12150, tp12150, tm12150, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12150, agent12150, scalar12150, tp12150, tm12150, ep12150, em12150, dsL]

theorem negative12150 :
    Eminus aL (agent12150.root+dsL) scalar12150.worldRadius world12150.frame
      agent12150.frame tm12150 ≤ -em12150 := by
  apply negative_check (lo := (33887512132477999667 / 50000000000000000000)) (hi := (13555004852991199867 / 20000000000000000000))
    (y := (-((36651792172422668711 / 50000000000000000000)))) (u := (48044820831420073443 / 100000000000000000000))
  · norm_num [world12150, agent12150, scalar12150, tp12150, tm12150, ep12150, em12150, dsL]
  · norm_num [world12150, agent12150, scalar12150, tp12150, tm12150, ep12150, em12150, dsL]
  · norm_num [world12150, agent12150, scalar12150, tp12150, tm12150, ep12150, em12150, dsL]
  · norm_num [world12150, agent12150, scalar12150, tp12150, tm12150, ep12150, em12150, dsL]
  · norm_num [world12150, agent12150, scalar12150, tp12150, tm12150, ep12150, em12150, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12150, agent12150, tp12150, tm12150, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12150, agent12150, tp12150, tm12150, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12150, agent12150, scalar12150, tp12150, tm12150, ep12150, em12150, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12150, agent12150, tp12150, tm12150, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12150, agent12150, scalar12150, tp12150, tm12150, ep12150, em12150, dsL]

theorem tails12150 :
    exp (-((12150:ℝ)*ep12150)) ≤ scalar12150.upperTail ∧
    exp (-((12150:ℝ)*em12150)) ≤ scalar12150.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12150:ℝ)) (by norm_num [ep12150]) ?_)
      (show bp12150^8 ≤ scalar12150.upperTail by norm_num [bp12150, scalar12150])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12150, bp12150, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12150:ℝ)) (by norm_num [em12150]) ?_)
      (show bm12150^8 ≤ scalar12150.lowerTail by norm_num [bm12150, scalar12150])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12150, bm12150, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12150 :
    agent12150.root+dsL+scalar12150.worldRadius < √(1/100/aL) ∧
    2*(agent12150.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12150, agent12150, scalar12150, tp12150, tm12150, ep12150, em12150, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12150, agent12150, scalar12150, tp12150, tm12150, ep12150, em12150, dsL]

noncomputable def master12150 : MasterCertificate 12150 world12150 agent12150 :=
  master scalar12150 dsL tp12150 tm12150 ep12150 em12150
    (by norm_num [dsL]) (by norm_num [tp12150]) (by norm_num [tm12150])
    (by norm_num [ep12150]) (by norm_num [em12150])
    positive12150 negative12150 tails12150.1 tails12150.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12150.1 tailGuards12150.2

theorem preserves12150 : master12150.toScalarCertificate = scalar12150 := rfl

noncomputable def tp12151 : ℝ := (148319329 / 625000000)
noncomputable def tm12151 : ℝ := (-((3069718373 / 5000000000)))
noncomputable def ep12151 : ℝ := (54602029532369457 / 100000000000000000000)
noncomputable def em12151 : ℝ := (52644748566424979 / 100000000000000000000)
noncomputable def bp12151 : ℝ := (43633866783789771571 / 100000000000000000000)
noncomputable def bm12151 : ℝ := (22475258470328114131 / 50000000000000000000)

theorem positive12151 :
    Eplus aL (agent12151.root+dsL) scalar12151.worldRadius world12151.frame
      agent12151.frame tp12151 ≤ -ep12151 := by
  apply positive_check (eT := (58112335670234267149 / 50000000000000000000)) (y := (39627910187050704659 / 100000000000000000000)) (u := (148628408433564749029 / 100000000000000000000))
  · norm_num [world12151, agent12151, scalar12151, tp12151, tm12151, ep12151, em12151, dsL]
  · norm_num [world12151, agent12151, scalar12151, tp12151, tm12151, ep12151, em12151, dsL]
  · norm_num [world12151, agent12151, scalar12151, tp12151, tm12151, ep12151, em12151, dsL]
  · norm_num [world12151, agent12151, scalar12151, tp12151, tm12151, ep12151, em12151, dsL]
  · norm_num [world12151, agent12151, scalar12151, tp12151, tm12151, ep12151, em12151, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12151, agent12151, tp12151, tm12151, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12151, agent12151, scalar12151, tp12151, tm12151, ep12151, em12151, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12151, agent12151, tp12151, tm12151, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12151, agent12151, scalar12151, tp12151, tm12151, ep12151, em12151, dsL]

theorem negative12151 :
    Eminus aL (agent12151.root+dsL) scalar12151.worldRadius world12151.frame
      agent12151.frame tm12151 ≤ -em12151 := by
  apply negative_check (lo := (6777470575054016609 / 10000000000000000000)) (hi := (67774705750540166091 / 100000000000000000000))
    (y := (-((73303185819316006121 / 100000000000000000000)))) (u := (12011253075669534701 / 25000000000000000000))
  · norm_num [world12151, agent12151, scalar12151, tp12151, tm12151, ep12151, em12151, dsL]
  · norm_num [world12151, agent12151, scalar12151, tp12151, tm12151, ep12151, em12151, dsL]
  · norm_num [world12151, agent12151, scalar12151, tp12151, tm12151, ep12151, em12151, dsL]
  · norm_num [world12151, agent12151, scalar12151, tp12151, tm12151, ep12151, em12151, dsL]
  · norm_num [world12151, agent12151, scalar12151, tp12151, tm12151, ep12151, em12151, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12151, agent12151, tp12151, tm12151, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12151, agent12151, tp12151, tm12151, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12151, agent12151, scalar12151, tp12151, tm12151, ep12151, em12151, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12151, agent12151, tp12151, tm12151, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12151, agent12151, scalar12151, tp12151, tm12151, ep12151, em12151, dsL]

theorem tails12151 :
    exp (-((12151:ℝ)*ep12151)) ≤ scalar12151.upperTail ∧
    exp (-((12151:ℝ)*em12151)) ≤ scalar12151.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12151:ℝ)) (by norm_num [ep12151]) ?_)
      (show bp12151^8 ≤ scalar12151.upperTail by norm_num [bp12151, scalar12151])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12151, bp12151, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12151:ℝ)) (by norm_num [em12151]) ?_)
      (show bm12151^8 ≤ scalar12151.lowerTail by norm_num [bm12151, scalar12151])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12151, bm12151, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12151 :
    agent12151.root+dsL+scalar12151.worldRadius < √(1/100/aL) ∧
    2*(agent12151.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12151, agent12151, scalar12151, tp12151, tm12151, ep12151, em12151, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12151, agent12151, scalar12151, tp12151, tm12151, ep12151, em12151, dsL]

noncomputable def master12151 : MasterCertificate 12151 world12151 agent12151 :=
  master scalar12151 dsL tp12151 tm12151 ep12151 em12151
    (by norm_num [dsL]) (by norm_num [tp12151]) (by norm_num [tm12151])
    (by norm_num [ep12151]) (by norm_num [em12151])
    positive12151 negative12151 tails12151.1 tails12151.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12151.1 tailGuards12151.2

theorem preserves12151 : master12151.toScalarCertificate = scalar12151 := rfl

noncomputable def tp12152 : ℝ := (2373207757 / 10000000000)
noncomputable def tm12152 : ℝ := (-((6139657791 / 10000000000)))
noncomputable def ep12152 : ℝ := (10920983344873331 / 20000000000000000000)
noncomputable def em12152 : ℝ := (52647257848030669 / 100000000000000000000)
noncomputable def bp12152 : ℝ := (21814487654769555449 / 50000000000000000000)
noncomputable def bm12152 : ℝ := (11236461459800405649 / 25000000000000000000)

theorem positive12152 :
    Eplus aL (agent12152.root+dsL) scalar12152.worldRadius world12152.frame
      agent12152.frame tp12152 ≤ -ep12152 := by
  apply positive_check (eT := (29056244665032155587 / 25000000000000000000)) (y := (19814268630977208713 / 50000000000000000000)) (u := (3715733511198400867 / 2500000000000000000))
  · norm_num [world12152, agent12152, scalar12152, tp12152, tm12152, ep12152, em12152, dsL]
  · norm_num [world12152, agent12152, scalar12152, tp12152, tm12152, ep12152, em12152, dsL]
  · norm_num [world12152, agent12152, scalar12152, tp12152, tm12152, ep12152, em12152, dsL]
  · norm_num [world12152, agent12152, scalar12152, tp12152, tm12152, ep12152, em12152, dsL]
  · norm_num [world12152, agent12152, scalar12152, tp12152, tm12152, ep12152, em12152, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12152, agent12152, tp12152, tm12152, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12152, agent12152, scalar12152, tp12152, tm12152, ep12152, em12152, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12152, agent12152, tp12152, tm12152, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12152, agent12152, scalar12152, tp12152, tm12152, ep12152, em12152, dsL]

theorem negative12152 :
    Eminus aL (agent12152.root+dsL) scalar12152.worldRadius world12152.frame
      agent12152.frame tm12152 ≤ -em12152 := by
  apply negative_check (lo := (6777438710759200547 / 10000000000000000000)) (hi := (67774387107592005471 / 100000000000000000000))
    (y := (-((73302788666970750839 / 100000000000000000000)))) (u := (9609040622990036907 / 20000000000000000000))
  · norm_num [world12152, agent12152, scalar12152, tp12152, tm12152, ep12152, em12152, dsL]
  · norm_num [world12152, agent12152, scalar12152, tp12152, tm12152, ep12152, em12152, dsL]
  · norm_num [world12152, agent12152, scalar12152, tp12152, tm12152, ep12152, em12152, dsL]
  · norm_num [world12152, agent12152, scalar12152, tp12152, tm12152, ep12152, em12152, dsL]
  · norm_num [world12152, agent12152, scalar12152, tp12152, tm12152, ep12152, em12152, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12152, agent12152, tp12152, tm12152, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12152, agent12152, tp12152, tm12152, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12152, agent12152, scalar12152, tp12152, tm12152, ep12152, em12152, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12152, agent12152, tp12152, tm12152, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12152, agent12152, scalar12152, tp12152, tm12152, ep12152, em12152, dsL]

theorem tails12152 :
    exp (-((12152:ℝ)*ep12152)) ≤ scalar12152.upperTail ∧
    exp (-((12152:ℝ)*em12152)) ≤ scalar12152.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12152:ℝ)) (by norm_num [ep12152]) ?_)
      (show bp12152^8 ≤ scalar12152.upperTail by norm_num [bp12152, scalar12152])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12152, bp12152, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12152:ℝ)) (by norm_num [em12152]) ?_)
      (show bm12152^8 ≤ scalar12152.lowerTail by norm_num [bm12152, scalar12152])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12152, bm12152, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12152 :
    agent12152.root+dsL+scalar12152.worldRadius < √(1/100/aL) ∧
    2*(agent12152.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12152, agent12152, scalar12152, tp12152, tm12152, ep12152, em12152, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12152, agent12152, scalar12152, tp12152, tm12152, ep12152, em12152, dsL]

noncomputable def master12152 : MasterCertificate 12152 world12152 agent12152 :=
  master scalar12152 dsL tp12152 tm12152 ep12152 em12152
    (by norm_num [dsL]) (by norm_num [tp12152]) (by norm_num [tm12152])
    (by norm_num [ep12152]) (by norm_num [em12152])
    positive12152 negative12152 tails12152.1 tails12152.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12152.1 tailGuards12152.2

theorem preserves12152 : master12152.toScalarCertificate = scalar12152 := rfl

noncomputable def tp12153 : ℝ := (74165819 / 312500000)
noncomputable def tm12153 : ℝ := (-((3069939313 / 5000000000)))
noncomputable def ep12153 : ℝ := (54607801589295237 / 100000000000000000000)
noncomputable def em12153 : ℝ := (13162441251769697 / 25000000000000000000)
noncomputable def bp12153 : ℝ := (21812042805458356069 / 50000000000000000000)
noncomputable def bm12153 : ℝ := (280882352439520959 / 625000000000000000)

theorem positive12153 :
    Eplus aL (agent12153.root+dsL) scalar12153.worldRadius world12153.frame
      agent12153.frame tp12153 ≤ -ep12153 := by
  apply positive_check (eT := (7264080356715798581 / 6250000000000000000)) (y := (39629164143252877349 / 100000000000000000000)) (u := (7431513609019787617 / 5000000000000000000))
  · norm_num [world12153, agent12153, scalar12153, tp12153, tm12153, ep12153, em12153, dsL]
  · norm_num [world12153, agent12153, scalar12153, tp12153, tm12153, ep12153, em12153, dsL]
  · norm_num [world12153, agent12153, scalar12153, tp12153, tm12153, ep12153, em12153, dsL]
  · norm_num [world12153, agent12153, scalar12153, tp12153, tm12153, ep12153, em12153, dsL]
  · norm_num [world12153, agent12153, scalar12153, tp12153, tm12153, ep12153, em12153, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12153, agent12153, tp12153, tm12153, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12153, agent12153, scalar12153, tp12153, tm12153, ep12153, em12153, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12153, agent12153, tp12153, tm12153, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12153, agent12153, scalar12153, tp12153, tm12153, ep12153, em12153, dsL]

theorem negative12153 :
    Eminus aL (agent12153.root+dsL) scalar12153.worldRadius world12153.frame
      agent12153.frame tm12153 ≤ -em12153 := by
  apply negative_check (lo := (33887034653212257771 / 50000000000000000000)) (hi := (67774069306424515543 / 100000000000000000000))
    (y := (-((73302390246812523353 / 100000000000000000000)))) (u := (48045394537105787811 / 100000000000000000000))
  · norm_num [world12153, agent12153, scalar12153, tp12153, tm12153, ep12153, em12153, dsL]
  · norm_num [world12153, agent12153, scalar12153, tp12153, tm12153, ep12153, em12153, dsL]
  · norm_num [world12153, agent12153, scalar12153, tp12153, tm12153, ep12153, em12153, dsL]
  · norm_num [world12153, agent12153, scalar12153, tp12153, tm12153, ep12153, em12153, dsL]
  · norm_num [world12153, agent12153, scalar12153, tp12153, tm12153, ep12153, em12153, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12153, agent12153, tp12153, tm12153, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12153, agent12153, tp12153, tm12153, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12153, agent12153, scalar12153, tp12153, tm12153, ep12153, em12153, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12153, agent12153, tp12153, tm12153, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12153, agent12153, scalar12153, tp12153, tm12153, ep12153, em12153, dsL]

theorem tails12153 :
    exp (-((12153:ℝ)*ep12153)) ≤ scalar12153.upperTail ∧
    exp (-((12153:ℝ)*em12153)) ≤ scalar12153.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12153:ℝ)) (by norm_num [ep12153]) ?_)
      (show bp12153^8 ≤ scalar12153.upperTail by norm_num [bp12153, scalar12153])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12153, bp12153, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12153:ℝ)) (by norm_num [em12153]) ?_)
      (show bm12153^8 ≤ scalar12153.lowerTail by norm_num [bm12153, scalar12153])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12153, bm12153, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12153 :
    agent12153.root+dsL+scalar12153.worldRadius < √(1/100/aL) ∧
    2*(agent12153.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12153, agent12153, scalar12153, tp12153, tm12153, ep12153, em12153, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12153, agent12153, scalar12153, tp12153, tm12153, ep12153, em12153, dsL]

noncomputable def master12153 : MasterCertificate 12153 world12153 agent12153 :=
  master scalar12153 dsL tp12153 tm12153 ep12153 em12153
    (by norm_num [dsL]) (by norm_num [tp12153]) (by norm_num [tm12153])
    (by norm_num [ep12153]) (by norm_num [em12153])
    positive12153 negative12153 tails12153.1 tails12153.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12153.1 tailGuards12153.2

theorem preserves12153 : master12153.toScalarCertificate = scalar12153 := rfl

noncomputable def tp12154 : ℝ := (2373404639 / 10000000000)
noncomputable def tm12154 : ℝ := (-((767512423 / 1250000000)))
noncomputable def ep12154 : ℝ := (54610684675514207 / 100000000000000000000)
noncomputable def em12154 : ℝ := (26326135242435471 / 50000000000000000000)
noncomputable def bp12154 : ℝ := (1090479933111000183 / 2500000000000000000)
noncomputable def bm12154 : ℝ := (1797460331707567977 / 4000000000000000000)

theorem positive12154 :
    Eplus aL (agent12154.root+dsL) scalar12154.worldRadius world12154.frame
      agent12154.frame tp12154 ≤ -ep12154 := by
  apply positive_check (eT := (11622559264435139553 / 10000000000000000000)) (y := (39629791495528507441 / 100000000000000000000)) (u := (148631204618715384703 / 100000000000000000000))
  · norm_num [world12154, agent12154, scalar12154, tp12154, tm12154, ep12154, em12154, dsL]
  · norm_num [world12154, agent12154, scalar12154, tp12154, tm12154, ep12154, em12154, dsL]
  · norm_num [world12154, agent12154, scalar12154, tp12154, tm12154, ep12154, em12154, dsL]
  · norm_num [world12154, agent12154, scalar12154, tp12154, tm12154, ep12154, em12154, dsL]
  · norm_num [world12154, agent12154, scalar12154, tp12154, tm12154, ep12154, em12154, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12154, agent12154, tp12154, tm12154, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12154, agent12154, scalar12154, tp12154, tm12154, ep12154, em12154, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12154, agent12154, tp12154, tm12154, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12154, agent12154, scalar12154, tp12154, tm12154, ep12154, em12154, dsL]

theorem negative12154 :
    Eminus aL (agent12154.root+dsL) scalar12154.worldRadius world12154.frame
      agent12154.frame tm12154 ≤ -em12154 := by
  apply negative_check (lo := (33886875888027870589 / 50000000000000000000)) (hi := (67773751776055741179 / 100000000000000000000))
    (y := (-((18325498145486849591 / 25000000000000000000)))) (u := (24022792798569530811 / 50000000000000000000))
  · norm_num [world12154, agent12154, scalar12154, tp12154, tm12154, ep12154, em12154, dsL]
  · norm_num [world12154, agent12154, scalar12154, tp12154, tm12154, ep12154, em12154, dsL]
  · norm_num [world12154, agent12154, scalar12154, tp12154, tm12154, ep12154, em12154, dsL]
  · norm_num [world12154, agent12154, scalar12154, tp12154, tm12154, ep12154, em12154, dsL]
  · norm_num [world12154, agent12154, scalar12154, tp12154, tm12154, ep12154, em12154, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12154, agent12154, tp12154, tm12154, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12154, agent12154, tp12154, tm12154, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12154, agent12154, scalar12154, tp12154, tm12154, ep12154, em12154, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12154, agent12154, tp12154, tm12154, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12154, agent12154, scalar12154, tp12154, tm12154, ep12154, em12154, dsL]

theorem tails12154 :
    exp (-((12154:ℝ)*ep12154)) ≤ scalar12154.upperTail ∧
    exp (-((12154:ℝ)*em12154)) ≤ scalar12154.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12154:ℝ)) (by norm_num [ep12154]) ?_)
      (show bp12154^8 ≤ scalar12154.upperTail by norm_num [bp12154, scalar12154])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12154, bp12154, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12154:ℝ)) (by norm_num [em12154]) ?_)
      (show bm12154^8 ≤ scalar12154.lowerTail by norm_num [bm12154, scalar12154])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12154, bm12154, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12154 :
    agent12154.root+dsL+scalar12154.worldRadius < √(1/100/aL) ∧
    2*(agent12154.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12154, agent12154, scalar12154, tp12154, tm12154, ep12154, em12154, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12154, agent12154, scalar12154, tp12154, tm12154, ep12154, em12154, dsL]

noncomputable def master12154 : MasterCertificate 12154 world12154 agent12154 :=
  master scalar12154 dsL tp12154 tm12154 ep12154 em12154
    (by norm_num [dsL]) (by norm_num [tp12154]) (by norm_num [tm12154])
    (by norm_num [ep12154]) (by norm_num [em12154])
    positive12154 negative12154 tails12154.1 tails12154.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12154.1 tailGuards12154.2

theorem preserves12154 : master12154.toScalarCertificate = scalar12154 := rfl

noncomputable def tp12155 : ℝ := (474700591 / 2000000000)
noncomputable def tm12155 : ℝ := (-((6140319961 / 10000000000)))
noncomputable def ep12155 : ℝ := (54613567133966211 / 100000000000000000000)
noncomputable def em12155 : ℝ := (52654775348163041 / 100000000000000000000)
noncomputable def bp12155 : ℝ := (5451788710919835123 / 12500000000000000000)
noncomputable def bm12155 : ℝ := (5616480102250730963 / 12500000000000000000)

theorem positive12155 :
    Eplus aL (agent12155.root+dsL) scalar12155.worldRadius world12155.frame
      agent12155.frame tp12155 ≤ -ep12155 := by
  apply positive_check (eT := (116225898771402528667 / 100000000000000000000)) (y := (39630417239530584389 / 100000000000000000000)) (u := (148632134672473375799 / 100000000000000000000))
  · norm_num [world12155, agent12155, scalar12155, tp12155, tm12155, ep12155, em12155, dsL]
  · norm_num [world12155, agent12155, scalar12155, tp12155, tm12155, ep12155, em12155, dsL]
  · norm_num [world12155, agent12155, scalar12155, tp12155, tm12155, ep12155, em12155, dsL]
  · norm_num [world12155, agent12155, scalar12155, tp12155, tm12155, ep12155, em12155, dsL]
  · norm_num [world12155, agent12155, scalar12155, tp12155, tm12155, ep12155, em12155, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12155, agent12155, tp12155, tm12155, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12155, agent12155, scalar12155, tp12155, tm12155, ep12155, em12155, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12155, agent12155, tp12155, tm12155, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12155, agent12155, scalar12155, tp12155, tm12155, ep12155, em12155, dsL]

theorem negative12155 :
    Eminus aL (agent12155.root+dsL) scalar12155.worldRadius world12155.frame
      agent12155.frame tm12155 ≤ -em12155 := by
  apply negative_check (lo := (67773434962894121199 / 100000000000000000000)) (hi := (169433587407235303 / 250000000000000000))
    (y := (-((73301594197268574969 / 100000000000000000000)))) (u := (48045777003772198701 / 100000000000000000000))
  · norm_num [world12155, agent12155, scalar12155, tp12155, tm12155, ep12155, em12155, dsL]
  · norm_num [world12155, agent12155, scalar12155, tp12155, tm12155, ep12155, em12155, dsL]
  · norm_num [world12155, agent12155, scalar12155, tp12155, tm12155, ep12155, em12155, dsL]
  · norm_num [world12155, agent12155, scalar12155, tp12155, tm12155, ep12155, em12155, dsL]
  · norm_num [world12155, agent12155, scalar12155, tp12155, tm12155, ep12155, em12155, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12155, agent12155, tp12155, tm12155, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12155, agent12155, tp12155, tm12155, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12155, agent12155, scalar12155, tp12155, tm12155, ep12155, em12155, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12155, agent12155, tp12155, tm12155, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12155, agent12155, scalar12155, tp12155, tm12155, ep12155, em12155, dsL]

theorem tails12155 :
    exp (-((12155:ℝ)*ep12155)) ≤ scalar12155.upperTail ∧
    exp (-((12155:ℝ)*em12155)) ≤ scalar12155.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12155:ℝ)) (by norm_num [ep12155]) ?_)
      (show bp12155^8 ≤ scalar12155.upperTail by norm_num [bp12155, scalar12155])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12155, bp12155, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12155:ℝ)) (by norm_num [em12155]) ?_)
      (show bm12155^8 ≤ scalar12155.lowerTail by norm_num [bm12155, scalar12155])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12155, bm12155, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12155 :
    agent12155.root+dsL+scalar12155.worldRadius < √(1/100/aL) ∧
    2*(agent12155.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12155, agent12155, scalar12155, tp12155, tm12155, ep12155, em12155, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12155, agent12155, scalar12155, tp12155, tm12155, ep12155, em12155, dsL]

noncomputable def master12155 : MasterCertificate 12155 world12155 agent12155 :=
  master scalar12155 dsL tp12155 tm12155 ep12155 em12155
    (by norm_num [dsL]) (by norm_num [tp12155]) (by norm_num [tm12155])
    (by norm_num [ep12155]) (by norm_num [em12155])
    positive12155 negative12155 tails12155.1 tails12155.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12155.1 tailGuards12155.2

theorem preserves12155 : master12155.toScalarCertificate = scalar12155 := rfl

noncomputable def tp12156 : ℝ := (593400319 / 2500000000)
noncomputable def tm12156 : ℝ := (-((383783777 / 625000000)))
noncomputable def ep12156 : ℝ := (5461644712364869 / 10000000000000000000)
noncomputable def em12156 : ℝ := (10531455588063979 / 20000000000000000000)
noncomputable def bp12156 : ℝ := (43609423919611335003 / 100000000000000000000)
noncomputable def bm12156 : ℝ := (44927175097215961723 / 100000000000000000000)

theorem positive12156 :
    Eplus aL (agent12156.root+dsL) scalar12156.worldRadius world12156.frame
      agent12156.frame tp12156 ≤ -ep12156 := by
  apply positive_check (eT := (11622620497216871441 / 10000000000000000000)) (y := (19815521897020890227 / 50000000000000000000)) (u := (37158266484183922317 / 25000000000000000000))
  · norm_num [world12156, agent12156, scalar12156, tp12156, tm12156, ep12156, em12156, dsL]
  · norm_num [world12156, agent12156, scalar12156, tp12156, tm12156, ep12156, em12156, dsL]
  · norm_num [world12156, agent12156, scalar12156, tp12156, tm12156, ep12156, em12156, dsL]
  · norm_num [world12156, agent12156, scalar12156, tp12156, tm12156, ep12156, em12156, dsL]
  · norm_num [world12156, agent12156, scalar12156, tp12156, tm12156, ep12156, em12156, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12156, agent12156, tp12156, tm12156, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12156, agent12156, scalar12156, tp12156, tm12156, ep12156, em12156, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12156, agent12156, tp12156, tm12156, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12156, agent12156, scalar12156, tp12156, tm12156, ep12156, em12156, dsL]

theorem negative12156 :
    Eminus aL (agent12156.root+dsL) scalar12156.worldRadius world12156.frame
      agent12156.frame tm12156 ≤ -em12156 := by
  apply negative_check (lo := (67773118544937486333 / 100000000000000000000)) (hi := (33886559272468743167 / 50000000000000000000))
    (y := (-((36650597927244112769 / 50000000000000000000)))) (u := (24022984195518672219 / 50000000000000000000))
  · norm_num [world12156, agent12156, scalar12156, tp12156, tm12156, ep12156, em12156, dsL]
  · norm_num [world12156, agent12156, scalar12156, tp12156, tm12156, ep12156, em12156, dsL]
  · norm_num [world12156, agent12156, scalar12156, tp12156, tm12156, ep12156, em12156, dsL]
  · norm_num [world12156, agent12156, scalar12156, tp12156, tm12156, ep12156, em12156, dsL]
  · norm_num [world12156, agent12156, scalar12156, tp12156, tm12156, ep12156, em12156, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12156, agent12156, tp12156, tm12156, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12156, agent12156, tp12156, tm12156, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12156, agent12156, scalar12156, tp12156, tm12156, ep12156, em12156, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12156, agent12156, tp12156, tm12156, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12156, agent12156, scalar12156, tp12156, tm12156, ep12156, em12156, dsL]

theorem tails12156 :
    exp (-((12156:ℝ)*ep12156)) ≤ scalar12156.upperTail ∧
    exp (-((12156:ℝ)*em12156)) ≤ scalar12156.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12156:ℝ)) (by norm_num [ep12156]) ?_)
      (show bp12156^8 ≤ scalar12156.upperTail by norm_num [bp12156, scalar12156])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12156, bp12156, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12156:ℝ)) (by norm_num [em12156]) ?_)
      (show bm12156^8 ≤ scalar12156.lowerTail by norm_num [bm12156, scalar12156])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12156, bm12156, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12156 :
    agent12156.root+dsL+scalar12156.worldRadius < √(1/100/aL) ∧
    2*(agent12156.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12156, agent12156, scalar12156, tp12156, tm12156, ep12156, em12156, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12156, agent12156, scalar12156, tp12156, tm12156, ep12156, em12156, dsL]

noncomputable def master12156 : MasterCertificate 12156 world12156 agent12156 :=
  master scalar12156 dsL tp12156 tm12156 ep12156 em12156
    (by norm_num [dsL]) (by norm_num [tp12156]) (by norm_num [tm12156])
    (by norm_num [ep12156]) (by norm_num [em12156])
    positive12156 negative12156 tails12156.1 tails12156.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12156.1 tailGuards12156.2

theorem preserves12156 : master12156.toScalarCertificate = scalar12156 := rfl

noncomputable def tp12157 : ℝ := (474739909 / 2000000000)
noncomputable def tm12157 : ℝ := (-((6140760727 / 10000000000)))
noncomputable def ep12157 : ℝ := (27309663169521889 / 50000000000000000000)
noncomputable def em12157 : ℝ := (52659779765263653 / 100000000000000000000)
noncomputable def bp12157 : ℝ := (43604538898289078921 / 100000000000000000000)
noncomputable def bm12157 : ℝ := (22461255051799205207 / 50000000000000000000)

theorem positive12157 :
    Eplus aL (agent12157.root+dsL) scalar12157.worldRadius world12157.frame
      agent12157.frame tp12157 ≤ -ep12157 := by
  apply positive_check (eT := (116226510826949580607 / 100000000000000000000)) (y := (39631670032479519289 / 100000000000000000000)) (u := (29726799347408057283 / 20000000000000000000))
  · norm_num [world12157, agent12157, scalar12157, tp12157, tm12157, ep12157, em12157, dsL]
  · norm_num [world12157, agent12157, scalar12157, tp12157, tm12157, ep12157, em12157, dsL]
  · norm_num [world12157, agent12157, scalar12157, tp12157, tm12157, ep12157, em12157, dsL]
  · norm_num [world12157, agent12157, scalar12157, tp12157, tm12157, ep12157, em12157, dsL]
  · norm_num [world12157, agent12157, scalar12157, tp12157, tm12157, ep12157, em12157, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12157, agent12157, tp12157, tm12157, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12157, agent12157, scalar12157, tp12157, tm12157, ep12157, em12157, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12157, agent12157, tp12157, tm12157, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12157, agent12157, scalar12157, tp12157, tm12157, ep12157, em12157, dsL]

theorem negative12157 :
    Eminus aL (agent12157.root+dsL) scalar12157.worldRadius world12157.frame
      agent12157.frame tm12157 ≤ -em12157 := by
  apply negative_check (lo := (67772802822710135353 / 100000000000000000000)) (hi := (33886401411355067677 / 50000000000000000000))
    (y := (-((36650398567649640061 / 50000000000000000000)))) (u := (12011539989978686209 / 25000000000000000000))
  · norm_num [world12157, agent12157, scalar12157, tp12157, tm12157, ep12157, em12157, dsL]
  · norm_num [world12157, agent12157, scalar12157, tp12157, tm12157, ep12157, em12157, dsL]
  · norm_num [world12157, agent12157, scalar12157, tp12157, tm12157, ep12157, em12157, dsL]
  · norm_num [world12157, agent12157, scalar12157, tp12157, tm12157, ep12157, em12157, dsL]
  · norm_num [world12157, agent12157, scalar12157, tp12157, tm12157, ep12157, em12157, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12157, agent12157, tp12157, tm12157, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12157, agent12157, tp12157, tm12157, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12157, agent12157, scalar12157, tp12157, tm12157, ep12157, em12157, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12157, agent12157, tp12157, tm12157, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12157, agent12157, scalar12157, tp12157, tm12157, ep12157, em12157, dsL]

theorem tails12157 :
    exp (-((12157:ℝ)*ep12157)) ≤ scalar12157.upperTail ∧
    exp (-((12157:ℝ)*em12157)) ≤ scalar12157.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12157:ℝ)) (by norm_num [ep12157]) ?_)
      (show bp12157^8 ≤ scalar12157.upperTail by norm_num [bp12157, scalar12157])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12157, bp12157, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12157:ℝ)) (by norm_num [em12157]) ?_)
      (show bm12157^8 ≤ scalar12157.lowerTail by norm_num [bm12157, scalar12157])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12157, bm12157, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12157 :
    agent12157.root+dsL+scalar12157.worldRadius < √(1/100/aL) ∧
    2*(agent12157.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12157, agent12157, scalar12157, tp12157, tm12157, ep12157, em12157, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12157, agent12157, scalar12157, tp12157, tm12157, ep12157, em12157, dsL]

noncomputable def master12157 : MasterCertificate 12157 world12157 agent12157 :=
  master scalar12157 dsL tp12157 tm12157 ep12157 em12157
    (by norm_num [dsL]) (by norm_num [tp12157]) (by norm_num [tm12157])
    (by norm_num [ep12157]) (by norm_num [em12157])
    positive12157 negative12157 tails12157.1 tails12157.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12157.1 tailGuards12157.2

theorem preserves12157 : master12157.toScalarCertificate = scalar12157 := rfl

noncomputable def tp12158 : ℝ := (1186898851 / 5000000000)
noncomputable def tm12158 : ℝ := (-((614098103 / 1000000000)))
noncomputable def ep12158 : ℝ := (27311101540580461 / 50000000000000000000)
noncomputable def em12158 : ℝ := (26331139657706013 / 50000000000000000000)
noncomputable def bp12158 : ℝ := (8719931149830242147 / 20000000000000000000)
noncomputable def bm12158 : ℝ := (44917846866290939251 / 100000000000000000000)

theorem positive12158 :
    Eplus aL (agent12158.root+dsL) scalar12158.worldRadius world12158.frame
      agent12158.frame tp12158 ≤ -ep12158 := by
  apply positive_check (eT := (116226815894047704379 / 100000000000000000000)) (y := (39632294976711272357 / 100000000000000000000)) (u := (18579365702441476793 / 12500000000000000000))
  · norm_num [world12158, agent12158, scalar12158, tp12158, tm12158, ep12158, em12158, dsL]
  · norm_num [world12158, agent12158, scalar12158, tp12158, tm12158, ep12158, em12158, dsL]
  · norm_num [world12158, agent12158, scalar12158, tp12158, tm12158, ep12158, em12158, dsL]
  · norm_num [world12158, agent12158, scalar12158, tp12158, tm12158, ep12158, em12158, dsL]
  · norm_num [world12158, agent12158, scalar12158, tp12158, tm12158, ep12158, em12158, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12158, agent12158, tp12158, tm12158, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12158, agent12158, scalar12158, tp12158, tm12158, ep12158, em12158, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12158, agent12158, tp12158, tm12158, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12158, agent12158, scalar12158, tp12158, tm12158, ep12158, em12158, dsL]

theorem negative12158 :
    Eminus aL (agent12158.root+dsL) scalar12158.worldRadius world12158.frame
      agent12158.frame tm12158 ≤ -em12158 := by
  apply negative_check (lo := (13554497401229390327 / 20000000000000000000)) (hi := (16943121751536737909 / 25000000000000000000))
    (y := (-((36650199784915754133 / 50000000000000000000)))) (u := (4804635097523504111 / 10000000000000000000))
  · norm_num [world12158, agent12158, scalar12158, tp12158, tm12158, ep12158, em12158, dsL]
  · norm_num [world12158, agent12158, scalar12158, tp12158, tm12158, ep12158, em12158, dsL]
  · norm_num [world12158, agent12158, scalar12158, tp12158, tm12158, ep12158, em12158, dsL]
  · norm_num [world12158, agent12158, scalar12158, tp12158, tm12158, ep12158, em12158, dsL]
  · norm_num [world12158, agent12158, scalar12158, tp12158, tm12158, ep12158, em12158, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12158, agent12158, tp12158, tm12158, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12158, agent12158, tp12158, tm12158, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12158, agent12158, scalar12158, tp12158, tm12158, ep12158, em12158, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12158, agent12158, tp12158, tm12158, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12158, agent12158, scalar12158, tp12158, tm12158, ep12158, em12158, dsL]

theorem tails12158 :
    exp (-((12158:ℝ)*ep12158)) ≤ scalar12158.upperTail ∧
    exp (-((12158:ℝ)*em12158)) ≤ scalar12158.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12158:ℝ)) (by norm_num [ep12158]) ?_)
      (show bp12158^8 ≤ scalar12158.upperTail by norm_num [bp12158, scalar12158])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12158, bp12158, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12158:ℝ)) (by norm_num [em12158]) ?_)
      (show bm12158^8 ≤ scalar12158.lowerTail by norm_num [bm12158, scalar12158])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12158, bm12158, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12158 :
    agent12158.root+dsL+scalar12158.worldRadius < √(1/100/aL) ∧
    2*(agent12158.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12158, agent12158, scalar12158, tp12158, tm12158, ep12158, em12158, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12158, agent12158, scalar12158, tp12158, tm12158, ep12158, em12158, dsL]

noncomputable def master12158 : MasterCertificate 12158 world12158 agent12158 :=
  master scalar12158 dsL tp12158 tm12158 ep12158 em12158
    (by norm_num [dsL]) (by norm_num [tp12158]) (by norm_num [tm12158])
    (by norm_num [ep12158]) (by norm_num [em12158])
    positive12158 negative12158 tails12158.1 tails12158.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12158.1 tailGuards12158.2

theorem preserves12158 : master12158.toScalarCertificate = scalar12158 := rfl

end BstLean.Part281
