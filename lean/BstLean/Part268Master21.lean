import BstLean.Part261Checker
import BstLean.Part268Scalar21
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12875 : ℝ := (466429207 / 2000000000)
noncomputable def tm12875 : ℝ := (-((1524376401 / 2500000000)))
noncomputable def ep12875 : ℝ := (51889190135749497 / 100000000000000000000)
noncomputable def em12875 : ℝ := (50512714674431807 / 100000000000000000000)
noncomputable def bp12875 : ℝ := (21691735851662553047 / 50000000000000000000)
noncomputable def bm12875 : ℝ := (22177627348536267899 / 50000000000000000000)

theorem positive12875 :
    Eplus aL (agent12875.root+dsL) scalar12875.worldRadius world12875.frame
      agent12875.frame tp12875 ≤ -ep12875 := by
  apply positive_check (eT := (115644208106289397639 / 100000000000000000000)) (y := (37982371276236429781 / 100000000000000000000)) (u := (73101341502191445271 / 50000000000000000000))
  · norm_num [world12875, agent12875, scalar12875, tp12875, tm12875, ep12875, em12875, dsL]
  · norm_num [world12875, agent12875, scalar12875, tp12875, tm12875, ep12875, em12875, dsL]
  · norm_num [world12875, agent12875, scalar12875, tp12875, tm12875, ep12875, em12875, dsL]
  · norm_num [world12875, agent12875, scalar12875, tp12875, tm12875, ep12875, em12875, dsL]
  · norm_num [world12875, agent12875, scalar12875, tp12875, tm12875, ep12875, em12875, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12875, agent12875, tp12875, tm12875, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12875, agent12875, scalar12875, tp12875, tm12875, ep12875, em12875, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12875, agent12875, tp12875, tm12875, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12875, agent12875, scalar12875, tp12875, tm12875, ep12875, em12875, dsL]

theorem negative12875 :
    Eminus aL (agent12875.root+dsL) scalar12875.worldRadius world12875.frame
      agent12875.frame tm12875 ≤ -em12875 := by
  apply negative_check (lo := (2137025224643225639 / 3125000000000000000)) (hi := (68384807188583220449 / 100000000000000000000))
    (y := (-((35830954408414142313 / 50000000000000000000)))) (u := (12210017687141699651 / 25000000000000000000))
  · norm_num [world12875, agent12875, scalar12875, tp12875, tm12875, ep12875, em12875, dsL]
  · norm_num [world12875, agent12875, scalar12875, tp12875, tm12875, ep12875, em12875, dsL]
  · norm_num [world12875, agent12875, scalar12875, tp12875, tm12875, ep12875, em12875, dsL]
  · norm_num [world12875, agent12875, scalar12875, tp12875, tm12875, ep12875, em12875, dsL]
  · norm_num [world12875, agent12875, scalar12875, tp12875, tm12875, ep12875, em12875, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12875, agent12875, tp12875, tm12875, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12875, agent12875, tp12875, tm12875, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12875, agent12875, scalar12875, tp12875, tm12875, ep12875, em12875, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12875, agent12875, tp12875, tm12875, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12875, agent12875, scalar12875, tp12875, tm12875, ep12875, em12875, dsL]

theorem tails12875 :
    exp (-((12875:ℝ)*ep12875)) ≤ scalar12875.upperTail ∧
    exp (-((12875:ℝ)*em12875)) ≤ scalar12875.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12875:ℝ)) (by norm_num [ep12875]) ?_)
      (show bp12875^8 ≤ scalar12875.upperTail by norm_num [bp12875, scalar12875])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12875, bp12875, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12875:ℝ)) (by norm_num [em12875]) ?_)
      (show bm12875^8 ≤ scalar12875.lowerTail by norm_num [bm12875, scalar12875])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12875, bm12875, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12875 :
    agent12875.root+dsL+scalar12875.worldRadius < √(1/100/aL) ∧
    2*(agent12875.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12875, agent12875, scalar12875, tp12875, tm12875, ep12875, em12875, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12875, agent12875, scalar12875, tp12875, tm12875, ep12875, em12875, dsL]

noncomputable def master12875 : MasterCertificate 12875 world12875 agent12875 :=
  master scalar12875 dsL tp12875 tm12875 ep12875 em12875
    (by norm_num [dsL]) (by norm_num [tp12875]) (by norm_num [tm12875])
    (by norm_num [ep12875]) (by norm_num [em12875])
    positive12875 negative12875 tails12875.1 tails12875.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12875.1 tailGuards12875.2

theorem preserves12875 : master12875.toScalarCertificate = scalar12875 := rfl

noncomputable def tp12876 : ℝ := (2332225407 / 10000000000)
noncomputable def tm12876 : ℝ := (-((6097675087 / 10000000000)))
noncomputable def ep12876 : ℝ := (51891605448062401 / 100000000000000000000)
noncomputable def em12876 : ℝ := (12628693962295067 / 25000000000000000000)
noncomputable def bp12876 : ℝ := (43378971511555722219 / 100000000000000000000)
noncomputable def bm12876 : ℝ := (44350982804226026491 / 100000000000000000000)

theorem positive12876 :
    Eplus aL (agent12876.root+dsL) scalar12876.worldRadius world12876.frame
      agent12876.frame tp12876 ≤ -ep12876 := by
  apply positive_check (eT := (115644417088063037091 / 100000000000000000000)) (y := (37983100062637188111 / 100000000000000000000)) (u := (29240749702707361697 / 20000000000000000000))
  · norm_num [world12876, agent12876, scalar12876, tp12876, tm12876, ep12876, em12876, dsL]
  · norm_num [world12876, agent12876, scalar12876, tp12876, tm12876, ep12876, em12876, dsL]
  · norm_num [world12876, agent12876, scalar12876, tp12876, tm12876, ep12876, em12876, dsL]
  · norm_num [world12876, agent12876, scalar12876, tp12876, tm12876, ep12876, em12876, dsL]
  · norm_num [world12876, agent12876, scalar12876, tp12876, tm12876, ep12876, em12876, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12876, agent12876, tp12876, tm12876, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12876, agent12876, scalar12876, tp12876, tm12876, ep12876, em12876, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12876, agent12876, tp12876, tm12876, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12876, agent12876, scalar12876, tp12876, tm12876, ep12876, em12876, dsL]

theorem negative12876 :
    Eminus aL (agent12876.root+dsL) scalar12876.worldRadius world12876.frame
      agent12876.frame tm12876 ≤ -em12876 := by
  apply negative_check (lo := (68384646204284487611 / 100000000000000000000)) (hi := (17096161551071121903 / 25000000000000000000))
    (y := (-((71661910555384408727 / 100000000000000000000)))) (u := (48840069899454764971 / 100000000000000000000))
  · norm_num [world12876, agent12876, scalar12876, tp12876, tm12876, ep12876, em12876, dsL]
  · norm_num [world12876, agent12876, scalar12876, tp12876, tm12876, ep12876, em12876, dsL]
  · norm_num [world12876, agent12876, scalar12876, tp12876, tm12876, ep12876, em12876, dsL]
  · norm_num [world12876, agent12876, scalar12876, tp12876, tm12876, ep12876, em12876, dsL]
  · norm_num [world12876, agent12876, scalar12876, tp12876, tm12876, ep12876, em12876, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12876, agent12876, tp12876, tm12876, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12876, agent12876, tp12876, tm12876, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12876, agent12876, scalar12876, tp12876, tm12876, ep12876, em12876, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12876, agent12876, tp12876, tm12876, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12876, agent12876, scalar12876, tp12876, tm12876, ep12876, em12876, dsL]

theorem tails12876 :
    exp (-((12876:ℝ)*ep12876)) ≤ scalar12876.upperTail ∧
    exp (-((12876:ℝ)*em12876)) ≤ scalar12876.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12876:ℝ)) (by norm_num [ep12876]) ?_)
      (show bp12876^8 ≤ scalar12876.upperTail by norm_num [bp12876, scalar12876])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12876, bp12876, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12876:ℝ)) (by norm_num [em12876]) ?_)
      (show bm12876^8 ≤ scalar12876.lowerTail by norm_num [bm12876, scalar12876])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12876, bm12876, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12876 :
    agent12876.root+dsL+scalar12876.worldRadius < √(1/100/aL) ∧
    2*(agent12876.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12876, agent12876, scalar12876, tp12876, tm12876, ep12876, em12876, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12876, agent12876, scalar12876, tp12876, tm12876, ep12876, em12876, dsL]

noncomputable def master12876 : MasterCertificate 12876 world12876 agent12876 :=
  master scalar12876 dsL tp12876 tm12876 ep12876 em12876
    (by norm_num [dsL]) (by norm_num [tp12876]) (by norm_num [tm12876])
    (by norm_num [ep12876]) (by norm_num [em12876])
    positive12876 negative12876 tails12876.1 tails12876.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12876.1 tailGuards12876.2

theorem preserves12876 : master12876.toScalarCertificate = scalar12876 := rfl

noncomputable def tp12877 : ℝ := (583076239 / 2500000000)
noncomputable def tm12877 : ℝ := (-((3048922427 / 5000000000)))
noncomputable def ep12877 : ℝ := (51894022923033647 / 100000000000000000000)
noncomputable def em12877 : ℝ := (5051683959169159 / 10000000000000000000)
noncomputable def bp12877 : ℝ := (43374470014791280227 / 100000000000000000000)
noncomputable def bm12877 : ℝ := (44346709261383868831 / 100000000000000000000)

theorem positive12877 :
    Eplus aL (agent12877.root+dsL) scalar12877.worldRadius world12877.frame
      agent12877.frame tp12877 ≤ -ep12877 := by
  apply positive_check (eT := (115644627378445250171 / 100000000000000000000)) (y := (18991913681794156783 / 50000000000000000000)) (u := (146204811858657183407 / 100000000000000000000))
  · norm_num [world12877, agent12877, scalar12877, tp12877, tm12877, ep12877, em12877, dsL]
  · norm_num [world12877, agent12877, scalar12877, tp12877, tm12877, ep12877, em12877, dsL]
  · norm_num [world12877, agent12877, scalar12877, tp12877, tm12877, ep12877, em12877, dsL]
  · norm_num [world12877, agent12877, scalar12877, tp12877, tm12877, ep12877, em12877, dsL]
  · norm_num [world12877, agent12877, scalar12877, tp12877, tm12877, ep12877, em12877, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12877, agent12877, tp12877, tm12877, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12877, agent12877, scalar12877, tp12877, tm12877, ep12877, em12877, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12877, agent12877, tp12877, tm12877, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12877, agent12877, scalar12877, tp12877, tm12877, ep12877, em12877, dsL]

theorem negative12877 :
    Eminus aL (agent12877.root+dsL) scalar12877.worldRadius world12877.frame
      agent12877.frame tm12877 ≤ -em12877 := by
  apply negative_check (lo := (3419224197632490197 / 5000000000000000000)) (hi := (68384483952649803941 / 100000000000000000000))
    (y := (-((17915476422691372481 / 25000000000000000000)))) (u := (9768014455067620609 / 20000000000000000000))
  · norm_num [world12877, agent12877, scalar12877, tp12877, tm12877, ep12877, em12877, dsL]
  · norm_num [world12877, agent12877, scalar12877, tp12877, tm12877, ep12877, em12877, dsL]
  · norm_num [world12877, agent12877, scalar12877, tp12877, tm12877, ep12877, em12877, dsL]
  · norm_num [world12877, agent12877, scalar12877, tp12877, tm12877, ep12877, em12877, dsL]
  · norm_num [world12877, agent12877, scalar12877, tp12877, tm12877, ep12877, em12877, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12877, agent12877, tp12877, tm12877, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12877, agent12877, tp12877, tm12877, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12877, agent12877, scalar12877, tp12877, tm12877, ep12877, em12877, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12877, agent12877, tp12877, tm12877, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12877, agent12877, scalar12877, tp12877, tm12877, ep12877, em12877, dsL]

theorem tails12877 :
    exp (-((12877:ℝ)*ep12877)) ≤ scalar12877.upperTail ∧
    exp (-((12877:ℝ)*em12877)) ≤ scalar12877.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12877:ℝ)) (by norm_num [ep12877]) ?_)
      (show bp12877^8 ≤ scalar12877.upperTail by norm_num [bp12877, scalar12877])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12877, bp12877, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12877:ℝ)) (by norm_num [em12877]) ?_)
      (show bm12877^8 ≤ scalar12877.lowerTail by norm_num [bm12877, scalar12877])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12877, bm12877, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12877 :
    agent12877.root+dsL+scalar12877.worldRadius < √(1/100/aL) ∧
    2*(agent12877.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12877, agent12877, scalar12877, tp12877, tm12877, ep12877, em12877, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12877, agent12877, scalar12877, tp12877, tm12877, ep12877, em12877, dsL]

noncomputable def master12877 : MasterCertificate 12877 world12877 agent12877 :=
  master scalar12877 dsL tp12877 tm12877 ep12877 em12877
    (by norm_num [dsL]) (by norm_num [tp12877]) (by norm_num [tm12877])
    (by norm_num [ep12877]) (by norm_num [em12877])
    positive12877 negative12877 tails12877.1 tails12877.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12877.1 tailGuards12877.2

theorem preserves12877 : master12877.toScalarCertificate = scalar12877 := rfl

noncomputable def tp12878 : ℝ := (93295379 / 400000000)
noncomputable def tm12878 : ℝ := (-((38112591 / 62500000)))
noncomputable def ep12878 : ℝ := (10379287756589639 / 20000000000000000000)
noncomputable def em12878 : ℝ := (98669730168771 / 195312500000000000)
noncomputable def bp12878 : ℝ := (677655778915432413 / 1562500000000000000)
noncomputable def bm12878 : ℝ := (22171218481770043803 / 50000000000000000000)

theorem positive12878 :
    Eplus aL (agent12878.root+dsL) scalar12878.worldRadius world12878.frame
      agent12878.frame tp12878 ≤ -ep12878 := by
  apply positive_check (eT := (28911209371374947177 / 25000000000000000000)) (y := (1899227723925184067 / 5000000000000000000)) (u := (29241174987903219631 / 20000000000000000000))
  · norm_num [world12878, agent12878, scalar12878, tp12878, tm12878, ep12878, em12878, dsL]
  · norm_num [world12878, agent12878, scalar12878, tp12878, tm12878, ep12878, em12878, dsL]
  · norm_num [world12878, agent12878, scalar12878, tp12878, tm12878, ep12878, em12878, dsL]
  · norm_num [world12878, agent12878, scalar12878, tp12878, tm12878, ep12878, em12878, dsL]
  · norm_num [world12878, agent12878, scalar12878, tp12878, tm12878, ep12878, em12878, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12878, agent12878, tp12878, tm12878, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12878, agent12878, scalar12878, tp12878, tm12878, ep12878, em12878, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12878, agent12878, tp12878, tm12878, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12878, agent12878, scalar12878, tp12878, tm12878, ep12878, em12878, dsL]

theorem negative12878 :
    Eminus aL (agent12878.root+dsL) scalar12878.worldRadius world12878.frame
      agent12878.frame tm12878 ≤ -em12878 := by
  apply negative_check (lo := (68384321904084723771 / 100000000000000000000)) (hi := (17096080476021180943 / 25000000000000000000))
    (y := (-((7166190061721552423 / 10000000000000000000)))) (u := (1953602990130545443 / 4000000000000000000))
  · norm_num [world12878, agent12878, scalar12878, tp12878, tm12878, ep12878, em12878, dsL]
  · norm_num [world12878, agent12878, scalar12878, tp12878, tm12878, ep12878, em12878, dsL]
  · norm_num [world12878, agent12878, scalar12878, tp12878, tm12878, ep12878, em12878, dsL]
  · norm_num [world12878, agent12878, scalar12878, tp12878, tm12878, ep12878, em12878, dsL]
  · norm_num [world12878, agent12878, scalar12878, tp12878, tm12878, ep12878, em12878, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12878, agent12878, tp12878, tm12878, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12878, agent12878, tp12878, tm12878, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12878, agent12878, scalar12878, tp12878, tm12878, ep12878, em12878, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12878, agent12878, tp12878, tm12878, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12878, agent12878, scalar12878, tp12878, tm12878, ep12878, em12878, dsL]

theorem tails12878 :
    exp (-((12878:ℝ)*ep12878)) ≤ scalar12878.upperTail ∧
    exp (-((12878:ℝ)*em12878)) ≤ scalar12878.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12878:ℝ)) (by norm_num [ep12878]) ?_)
      (show bp12878^8 ≤ scalar12878.upperTail by norm_num [bp12878, scalar12878])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12878, bp12878, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12878:ℝ)) (by norm_num [em12878]) ?_)
      (show bm12878^8 ≤ scalar12878.lowerTail by norm_num [bm12878, scalar12878])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12878, bm12878, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12878 :
    agent12878.root+dsL+scalar12878.worldRadius < √(1/100/aL) ∧
    2*(agent12878.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12878, agent12878, scalar12878, tp12878, tm12878, ep12878, em12878, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12878, agent12878, scalar12878, tp12878, tm12878, ep12878, em12878, dsL]

noncomputable def master12878 : MasterCertificate 12878 world12878 agent12878 :=
  master scalar12878 dsL tp12878 tm12878 ep12878 em12878
    (by norm_num [dsL]) (by norm_num [tp12878]) (by norm_num [tm12878])
    (by norm_num [ep12878]) (by norm_num [em12878])
    positive12878 negative12878 tails12878.1 tails12878.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12878.1 tailGuards12878.2

theorem preserves12878 : master12878.toScalarCertificate = scalar12878 := rfl

noncomputable def tp12879 : ℝ := (2332463909 / 10000000000)
noncomputable def tm12879 : ℝ := (-((6098184303 / 10000000000)))
noncomputable def ep12879 : ℝ := (6487356768027341 / 12500000000000000000)
noncomputable def em12879 : ℝ := (10104192721468371 / 20000000000000000000)
noncomputable def bp12879 : ℝ := (8673094047897732013 / 20000000000000000000)
noncomputable def bm12879 : ℝ := (44338165201152329697 / 100000000000000000000)

theorem positive12879 :
    Eplus aL (agent12879.root+dsL) scalar12879.worldRadius world12879.frame
      agent12879.frame tp12879 ≤ -ep12879 := by
  apply positive_check (eT := (115645047012870850197 / 100000000000000000000)) (y := (4748160062461495333 / 12500000000000000000)) (u := (36551734107249996439 / 25000000000000000000))
  · norm_num [world12879, agent12879, scalar12879, tp12879, tm12879, ep12879, em12879, dsL]
  · norm_num [world12879, agent12879, scalar12879, tp12879, tm12879, ep12879, em12879, dsL]
  · norm_num [world12879, agent12879, scalar12879, tp12879, tm12879, ep12879, em12879, dsL]
  · norm_num [world12879, agent12879, scalar12879, tp12879, tm12879, ep12879, em12879, dsL]
  · norm_num [world12879, agent12879, scalar12879, tp12879, tm12879, ep12879, em12879, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12879, agent12879, tp12879, tm12879, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12879, agent12879, scalar12879, tp12879, tm12879, ep12879, em12879, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12879, agent12879, tp12879, tm12879, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12879, agent12879, scalar12879, tp12879, tm12879, ep12879, em12879, dsL]

theorem negative12879 :
    Eminus aL (agent12879.root+dsL) scalar12879.worldRadius world12879.frame
      agent12879.frame tm12879 ≤ -em12879 := by
  apply negative_check (lo := (68384159640927740383 / 100000000000000000000)) (hi := (2137004988778991887 / 3125000000000000000))
    (y := (-((35830948413681301299 / 50000000000000000000)))) (u := (48840076604230671113 / 100000000000000000000))
  · norm_num [world12879, agent12879, scalar12879, tp12879, tm12879, ep12879, em12879, dsL]
  · norm_num [world12879, agent12879, scalar12879, tp12879, tm12879, ep12879, em12879, dsL]
  · norm_num [world12879, agent12879, scalar12879, tp12879, tm12879, ep12879, em12879, dsL]
  · norm_num [world12879, agent12879, scalar12879, tp12879, tm12879, ep12879, em12879, dsL]
  · norm_num [world12879, agent12879, scalar12879, tp12879, tm12879, ep12879, em12879, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12879, agent12879, tp12879, tm12879, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12879, agent12879, tp12879, tm12879, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12879, agent12879, scalar12879, tp12879, tm12879, ep12879, em12879, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12879, agent12879, tp12879, tm12879, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12879, agent12879, scalar12879, tp12879, tm12879, ep12879, em12879, dsL]

theorem tails12879 :
    exp (-((12879:ℝ)*ep12879)) ≤ scalar12879.upperTail ∧
    exp (-((12879:ℝ)*em12879)) ≤ scalar12879.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12879:ℝ)) (by norm_num [ep12879]) ?_)
      (show bp12879^8 ≤ scalar12879.upperTail by norm_num [bp12879, scalar12879])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12879, bp12879, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12879:ℝ)) (by norm_num [em12879]) ?_)
      (show bm12879^8 ≤ scalar12879.lowerTail by norm_num [bm12879, scalar12879])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12879, bm12879, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12879 :
    agent12879.root+dsL+scalar12879.worldRadius < √(1/100/aL) ∧
    2*(agent12879.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12879, agent12879, scalar12879, tp12879, tm12879, ep12879, em12879, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12879, agent12879, scalar12879, tp12879, tm12879, ep12879, em12879, dsL]

noncomputable def master12879 : MasterCertificate 12879 world12879 agent12879 :=
  master scalar12879 dsL tp12879 tm12879 ep12879 em12879
    (by norm_num [dsL]) (by norm_num [tp12879]) (by norm_num [tm12879])
    (by norm_num [ep12879]) (by norm_num [em12879])
    positive12879 negative12879 tails12879.1 tails12879.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12879.1 tailGuards12879.2

theorem preserves12879 : master12879.toScalarCertificate = scalar12879 := rfl

noncomputable def tp12880 : ℝ := (1166308123 / 5000000000)
noncomputable def tm12880 : ℝ := (-((6098574357 / 10000000000)))
noncomputable def ep12880 : ℝ := (51902652568730933 / 100000000000000000000)
noncomputable def em12880 : ℝ := (6315566747291231 / 12500000000000000000)
noncomputable def bp12880 : ℝ := (10840001327901518469 / 25000000000000000000)
noncomputable def bm12880 : ℝ := (11083204206417521111 / 25000000000000000000)

theorem positive12880 :
    Eplus aL (agent12880.root+dsL) scalar12880.worldRadius world12880.frame
      agent12880.frame tp12880 ≤ -ep12880 := by
  apply positive_check (eT := (14455722745274084689 / 12500000000000000000)) (y := (37985287888827226069 / 100000000000000000000)) (u := (29241389446485736423 / 20000000000000000000))
  · norm_num [world12880, agent12880, scalar12880, tp12880, tm12880, ep12880, em12880, dsL]
  · norm_num [world12880, agent12880, scalar12880, tp12880, tm12880, ep12880, em12880, dsL]
  · norm_num [world12880, agent12880, scalar12880, tp12880, tm12880, ep12880, em12880, dsL]
  · norm_num [world12880, agent12880, scalar12880, tp12880, tm12880, ep12880, em12880, dsL]
  · norm_num [world12880, agent12880, scalar12880, tp12880, tm12880, ep12880, em12880, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12880, agent12880, tp12880, tm12880, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12880, agent12880, scalar12880, tp12880, tm12880, ep12880, em12880, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12880, agent12880, tp12880, tm12880, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12880, agent12880, scalar12880, tp12880, tm12880, ep12880, em12880, dsL]

theorem negative12880 :
    Eminus aL (agent12880.root+dsL) scalar12880.worldRadius world12880.frame
      agent12880.frame tm12880 ≤ -em12880 := by
  apply negative_check (lo := (3419152923731082599 / 5000000000000000000)) (hi := (68383058474621651981 / 100000000000000000000))
    (y := (-((35830002711397591891 / 50000000000000000000)))) (u := (48841000376406401403 / 100000000000000000000))
  · norm_num [world12880, agent12880, scalar12880, tp12880, tm12880, ep12880, em12880, dsL]
  · norm_num [world12880, agent12880, scalar12880, tp12880, tm12880, ep12880, em12880, dsL]
  · norm_num [world12880, agent12880, scalar12880, tp12880, tm12880, ep12880, em12880, dsL]
  · norm_num [world12880, agent12880, scalar12880, tp12880, tm12880, ep12880, em12880, dsL]
  · norm_num [world12880, agent12880, scalar12880, tp12880, tm12880, ep12880, em12880, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12880, agent12880, tp12880, tm12880, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12880, agent12880, tp12880, tm12880, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12880, agent12880, scalar12880, tp12880, tm12880, ep12880, em12880, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12880, agent12880, tp12880, tm12880, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12880, agent12880, scalar12880, tp12880, tm12880, ep12880, em12880, dsL]

theorem tails12880 :
    exp (-((12880:ℝ)*ep12880)) ≤ scalar12880.upperTail ∧
    exp (-((12880:ℝ)*em12880)) ≤ scalar12880.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12880:ℝ)) (by norm_num [ep12880]) ?_)
      (show bp12880^8 ≤ scalar12880.upperTail by norm_num [bp12880, scalar12880])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12880, bp12880, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12880:ℝ)) (by norm_num [em12880]) ?_)
      (show bm12880^8 ≤ scalar12880.lowerTail by norm_num [bm12880, scalar12880])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12880, bm12880, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12880 :
    agent12880.root+dsL+scalar12880.worldRadius < √(1/100/aL) ∧
    2*(agent12880.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12880, agent12880, scalar12880, tp12880, tm12880, ep12880, em12880, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12880, agent12880, scalar12880, tp12880, tm12880, ep12880, em12880, dsL]

noncomputable def master12880 : MasterCertificate 12880 world12880 agent12880 :=
  master scalar12880 dsL tp12880 tm12880 ep12880 em12880
    (by norm_num [dsL]) (by norm_num [tp12880]) (by norm_num [tm12880])
    (by norm_num [ep12880]) (by norm_num [em12880])
    positive12880 negative12880 tails12880.1 tails12880.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12880.1 tailGuards12880.2

theorem preserves12880 : master12880.toScalarCertificate = scalar12880 := rfl

noncomputable def tp12881 : ℝ := (1166347809 / 5000000000)
noncomputable def tm12881 : ℝ := (-((1524685963 / 2500000000)))
noncomputable def ep12881 : ℝ := (25952532410255867 / 50000000000000000000)
noncomputable def em12881 : ℝ := (50526592884136329 / 100000000000000000000)
noncomputable def bp12881 : ℝ := (5419438538304782113 / 12500000000000000000)
noncomputable def bm12881 : ℝ := (2216427374365457107 / 5000000000000000000)

theorem positive12881 :
    Eplus aL (agent12881.root+dsL) scalar12881.worldRadius world12881.frame
      agent12881.frame tp12881 ≤ -ep12881 := by
  apply positive_check (eT := (115645991098199090943 / 100000000000000000000)) (y := (37986013529700207633 / 100000000000000000000)) (u := (146208008173646246107 / 100000000000000000000))
  · norm_num [world12881, agent12881, scalar12881, tp12881, tm12881, ep12881, em12881, dsL]
  · norm_num [world12881, agent12881, scalar12881, tp12881, tm12881, ep12881, em12881, dsL]
  · norm_num [world12881, agent12881, scalar12881, tp12881, tm12881, ep12881, em12881, dsL]
  · norm_num [world12881, agent12881, scalar12881, tp12881, tm12881, ep12881, em12881, dsL]
  · norm_num [world12881, agent12881, scalar12881, tp12881, tm12881, ep12881, em12881, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12881, agent12881, tp12881, tm12881, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12881, agent12881, scalar12881, tp12881, tm12881, ep12881, em12881, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12881, agent12881, tp12881, tm12881, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12881, agent12881, scalar12881, tp12881, tm12881, ep12881, em12881, dsL]

theorem negative12881 :
    Eminus aL (agent12881.root+dsL) scalar12881.worldRadius world12881.frame
      agent12881.frame tm12881 ≤ -em12881 := by
  apply negative_check (lo := (34191448588489068403 / 50000000000000000000)) (hi := (68382897176978136807 / 100000000000000000000))
    (y := (-((71660000311839551477 / 100000000000000000000)))) (u := (24420501436324162403 / 50000000000000000000))
  · norm_num [world12881, agent12881, scalar12881, tp12881, tm12881, ep12881, em12881, dsL]
  · norm_num [world12881, agent12881, scalar12881, tp12881, tm12881, ep12881, em12881, dsL]
  · norm_num [world12881, agent12881, scalar12881, tp12881, tm12881, ep12881, em12881, dsL]
  · norm_num [world12881, agent12881, scalar12881, tp12881, tm12881, ep12881, em12881, dsL]
  · norm_num [world12881, agent12881, scalar12881, tp12881, tm12881, ep12881, em12881, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12881, agent12881, tp12881, tm12881, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12881, agent12881, tp12881, tm12881, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12881, agent12881, scalar12881, tp12881, tm12881, ep12881, em12881, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12881, agent12881, tp12881, tm12881, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12881, agent12881, scalar12881, tp12881, tm12881, ep12881, em12881, dsL]

theorem tails12881 :
    exp (-((12881:ℝ)*ep12881)) ≤ scalar12881.upperTail ∧
    exp (-((12881:ℝ)*em12881)) ≤ scalar12881.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12881:ℝ)) (by norm_num [ep12881]) ?_)
      (show bp12881^8 ≤ scalar12881.upperTail by norm_num [bp12881, scalar12881])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12881, bp12881, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12881:ℝ)) (by norm_num [em12881]) ?_)
      (show bm12881^8 ≤ scalar12881.lowerTail by norm_num [bm12881, scalar12881])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12881, bm12881, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12881 :
    agent12881.root+dsL+scalar12881.worldRadius < √(1/100/aL) ∧
    2*(agent12881.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12881, agent12881, scalar12881, tp12881, tm12881, ep12881, em12881, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12881, agent12881, scalar12881, tp12881, tm12881, ep12881, em12881, dsL]

noncomputable def master12881 : MasterCertificate 12881 world12881 agent12881 :=
  master scalar12881 dsL tp12881 tm12881 ep12881 em12881
    (by norm_num [dsL]) (by norm_num [tp12881]) (by norm_num [tm12881])
    (by norm_num [ep12881]) (by norm_num [em12881])
    positive12881 negative12881 tails12881.1 tails12881.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12881.1 tailGuards12881.2

theorem preserves12881 : master12881.toScalarCertificate = scalar12881 := rfl

noncomputable def tp12882 : ℝ := (583193747 / 2500000000)
noncomputable def tm12882 : ℝ := (-((762364161 / 1250000000)))
noncomputable def ep12882 : ℝ := (51907475936889433 / 100000000000000000000)
noncomputable def em12882 : ℝ := (2021146029843609 / 4000000000000000000)
noncomputable def bp12882 : ℝ := (1734040491952579599 / 4000000000000000000)
noncomputable def bm12882 : ℝ := (22162139538487930197 / 50000000000000000000)

theorem positive12882 :
    Eplus aL (agent12882.root+dsL) scalar12882.worldRadius world12882.frame
      agent12882.frame tp12882 ≤ -ep12882 := by
  apply positive_check (eT := (57823100126348074683 / 50000000000000000000)) (y := (4748342428103769219 / 12500000000000000000)) (u := (146209069494309202671 / 100000000000000000000))
  · norm_num [world12882, agent12882, scalar12882, tp12882, tm12882, ep12882, em12882, dsL]
  · norm_num [world12882, agent12882, scalar12882, tp12882, tm12882, ep12882, em12882, dsL]
  · norm_num [world12882, agent12882, scalar12882, tp12882, tm12882, ep12882, em12882, dsL]
  · norm_num [world12882, agent12882, scalar12882, tp12882, tm12882, ep12882, em12882, dsL]
  · norm_num [world12882, agent12882, scalar12882, tp12882, tm12882, ep12882, em12882, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12882, agent12882, tp12882, tm12882, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12882, agent12882, scalar12882, tp12882, tm12882, ep12882, em12882, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12882, agent12882, tp12882, tm12882, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12882, agent12882, scalar12882, tp12882, tm12882, ep12882, em12882, dsL]

theorem negative12882 :
    Eminus aL (agent12882.root+dsL) scalar12882.worldRadius world12882.frame
      agent12882.frame tm12882 ≤ -em12882 := by
  apply negative_check (lo := (68382736073850733643 / 100000000000000000000)) (hi := (17095684018462683411 / 25000000000000000000))
    (y := (-((71659995138304024659 / 100000000000000000000)))) (u := (305256283746593909 / 625000000000000000))
  · norm_num [world12882, agent12882, scalar12882, tp12882, tm12882, ep12882, em12882, dsL]
  · norm_num [world12882, agent12882, scalar12882, tp12882, tm12882, ep12882, em12882, dsL]
  · norm_num [world12882, agent12882, scalar12882, tp12882, tm12882, ep12882, em12882, dsL]
  · norm_num [world12882, agent12882, scalar12882, tp12882, tm12882, ep12882, em12882, dsL]
  · norm_num [world12882, agent12882, scalar12882, tp12882, tm12882, ep12882, em12882, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12882, agent12882, tp12882, tm12882, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12882, agent12882, tp12882, tm12882, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12882, agent12882, scalar12882, tp12882, tm12882, ep12882, em12882, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12882, agent12882, tp12882, tm12882, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12882, agent12882, scalar12882, tp12882, tm12882, ep12882, em12882, dsL]

theorem tails12882 :
    exp (-((12882:ℝ)*ep12882)) ≤ scalar12882.upperTail ∧
    exp (-((12882:ℝ)*em12882)) ≤ scalar12882.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12882:ℝ)) (by norm_num [ep12882]) ?_)
      (show bp12882^8 ≤ scalar12882.upperTail by norm_num [bp12882, scalar12882])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12882, bp12882, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12882:ℝ)) (by norm_num [em12882]) ?_)
      (show bm12882^8 ≤ scalar12882.lowerTail by norm_num [bm12882, scalar12882])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12882, bm12882, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12882 :
    agent12882.root+dsL+scalar12882.worldRadius < √(1/100/aL) ∧
    2*(agent12882.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12882, agent12882, scalar12882, tp12882, tm12882, ep12882, em12882, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12882, agent12882, scalar12882, tp12882, tm12882, ep12882, em12882, dsL]

noncomputable def master12882 : MasterCertificate 12882 world12882 agent12882 :=
  master scalar12882 dsL tp12882 tm12882 ep12882 em12882
    (by norm_num [dsL]) (by norm_num [tp12882]) (by norm_num [tm12882])
    (by norm_num [ep12882]) (by norm_num [em12882])
    positive12882 negative12882 tails12882.1 tails12882.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12882.1 tailGuards12882.2

theorem preserves12882 : master12882.toScalarCertificate = scalar12882 := rfl

noncomputable def tp12883 : ℝ := (2332854279 / 10000000000)
noncomputable def tm12883 : ℝ := (-((6099082677 / 10000000000)))
noncomputable def ep12883 : ℝ := (10381977186397867 / 20000000000000000000)
noncomputable def em12883 : ℝ := (50530707521269667 / 100000000000000000000)
noncomputable def bp12883 : ℝ := (43346517278845670931 / 100000000000000000000)
noncomputable def bm12883 : ℝ := (22160005812644474163 / 50000000000000000000)

theorem positive12883 :
    Eplus aL (agent12883.root+dsL) scalar12883.worldRadius world12883.frame
      agent12883.frame tp12883 ≤ -ep12883 := by
  apply positive_check (eT := (115646408870807567137 / 100000000000000000000)) (y := (37987464532059502937 / 100000000000000000000)) (u := (146210129670685773211 / 100000000000000000000))
  · norm_num [world12883, agent12883, scalar12883, tp12883, tm12883, ep12883, em12883, dsL]
  · norm_num [world12883, agent12883, scalar12883, tp12883, tm12883, ep12883, em12883, dsL]
  · norm_num [world12883, agent12883, scalar12883, tp12883, tm12883, ep12883, em12883, dsL]
  · norm_num [world12883, agent12883, scalar12883, tp12883, tm12883, ep12883, em12883, dsL]
  · norm_num [world12883, agent12883, scalar12883, tp12883, tm12883, ep12883, em12883, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12883, agent12883, tp12883, tm12883, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12883, agent12883, scalar12883, tp12883, tm12883, ep12883, em12883, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12883, agent12883, tp12883, tm12883, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12883, agent12883, scalar12883, tp12883, tm12883, ep12883, em12883, dsL]

theorem negative12883 :
    Eminus aL (agent12883.root+dsL) scalar12883.worldRadius world12883.frame
      agent12883.frame tm12883 ≤ -em12883 := by
  apply negative_check (lo := (17095643778520234217 / 25000000000000000000)) (hi := (68382575114080936869 / 100000000000000000000))
    (y := (-((35829995297437470649 / 50000000000000000000)))) (u := (1953640304740460791 / 4000000000000000000))
  · norm_num [world12883, agent12883, scalar12883, tp12883, tm12883, ep12883, em12883, dsL]
  · norm_num [world12883, agent12883, scalar12883, tp12883, tm12883, ep12883, em12883, dsL]
  · norm_num [world12883, agent12883, scalar12883, tp12883, tm12883, ep12883, em12883, dsL]
  · norm_num [world12883, agent12883, scalar12883, tp12883, tm12883, ep12883, em12883, dsL]
  · norm_num [world12883, agent12883, scalar12883, tp12883, tm12883, ep12883, em12883, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12883, agent12883, tp12883, tm12883, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12883, agent12883, tp12883, tm12883, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12883, agent12883, scalar12883, tp12883, tm12883, ep12883, em12883, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12883, agent12883, tp12883, tm12883, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12883, agent12883, scalar12883, tp12883, tm12883, ep12883, em12883, dsL]

theorem tails12883 :
    exp (-((12883:ℝ)*ep12883)) ≤ scalar12883.upperTail ∧
    exp (-((12883:ℝ)*em12883)) ≤ scalar12883.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12883:ℝ)) (by norm_num [ep12883]) ?_)
      (show bp12883^8 ≤ scalar12883.upperTail by norm_num [bp12883, scalar12883])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12883, bp12883, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12883:ℝ)) (by norm_num [em12883]) ?_)
      (show bm12883^8 ≤ scalar12883.lowerTail by norm_num [bm12883, scalar12883])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12883, bm12883, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12883 :
    agent12883.root+dsL+scalar12883.worldRadius < √(1/100/aL) ∧
    2*(agent12883.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12883, agent12883, scalar12883, tp12883, tm12883, ep12883, em12883, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12883, agent12883, scalar12883, tp12883, tm12883, ep12883, em12883, dsL]

noncomputable def master12883 : MasterCertificate 12883 world12883 agent12883 :=
  master scalar12883 dsL tp12883 tm12883 ep12883 em12883
    (by norm_num [dsL]) (by norm_num [tp12883]) (by norm_num [tm12883])
    (by norm_num [ep12883]) (by norm_num [em12883])
    positive12883 negative12883 tails12883.1 tails12883.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12883.1 tailGuards12883.2

theorem preserves12883 : master12883.toScalarCertificate = scalar12883 := rfl

noncomputable def tp12884 : ℝ := (1166466787 / 5000000000)
noncomputable def tm12884 : ℝ := (-((3049625909 / 5000000000)))
noncomputable def ep12884 : ℝ := (12978073658622471 / 25000000000000000000)
noncomputable def em12884 : ℝ := (10106552629247843 / 20000000000000000000)
noncomputable def bp12884 : ℝ := (2167101168304496749 / 5000000000000000000)
noncomputable def bm12884 : ℝ := (11078936294376363281 / 25000000000000000000)

theorem positive12884 :
    Eplus aL (agent12884.root+dsL) scalar12884.worldRadius world12884.frame
      agent12884.frame tp12884 ≤ -ep12884 := by
  apply positive_check (eT := (57823308775341054519 / 50000000000000000000)) (y := (18994094922593589769 / 50000000000000000000)) (u := (1142274923092157671 / 781250000000000000))
  · norm_num [world12884, agent12884, scalar12884, tp12884, tm12884, ep12884, em12884, dsL]
  · norm_num [world12884, agent12884, scalar12884, tp12884, tm12884, ep12884, em12884, dsL]
  · norm_num [world12884, agent12884, scalar12884, tp12884, tm12884, ep12884, em12884, dsL]
  · norm_num [world12884, agent12884, scalar12884, tp12884, tm12884, ep12884, em12884, dsL]
  · norm_num [world12884, agent12884, scalar12884, tp12884, tm12884, ep12884, em12884, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12884, agent12884, tp12884, tm12884, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12884, agent12884, scalar12884, tp12884, tm12884, ep12884, em12884, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12884, agent12884, tp12884, tm12884, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12884, agent12884, scalar12884, tp12884, tm12884, ep12884, em12884, dsL]

theorem negative12884 :
    Eminus aL (agent12884.root+dsL) scalar12884.worldRadius world12884.frame
      agent12884.frame tm12884 ≤ -em12884 := by
  apply negative_check (lo := (8547801894264090711 / 12500000000000000000)) (hi := (68382415154112725689 / 100000000000000000000))
    (y := (-((71659983872902294081 / 100000000000000000000)))) (u := (2442050545079540143 / 5000000000000000000))
  · norm_num [world12884, agent12884, scalar12884, tp12884, tm12884, ep12884, em12884, dsL]
  · norm_num [world12884, agent12884, scalar12884, tp12884, tm12884, ep12884, em12884, dsL]
  · norm_num [world12884, agent12884, scalar12884, tp12884, tm12884, ep12884, em12884, dsL]
  · norm_num [world12884, agent12884, scalar12884, tp12884, tm12884, ep12884, em12884, dsL]
  · norm_num [world12884, agent12884, scalar12884, tp12884, tm12884, ep12884, em12884, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12884, agent12884, tp12884, tm12884, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12884, agent12884, tp12884, tm12884, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12884, agent12884, scalar12884, tp12884, tm12884, ep12884, em12884, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12884, agent12884, tp12884, tm12884, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12884, agent12884, scalar12884, tp12884, tm12884, ep12884, em12884, dsL]

theorem tails12884 :
    exp (-((12884:ℝ)*ep12884)) ≤ scalar12884.upperTail ∧
    exp (-((12884:ℝ)*em12884)) ≤ scalar12884.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12884:ℝ)) (by norm_num [ep12884]) ?_)
      (show bp12884^8 ≤ scalar12884.upperTail by norm_num [bp12884, scalar12884])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12884, bp12884, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12884:ℝ)) (by norm_num [em12884]) ?_)
      (show bm12884^8 ≤ scalar12884.lowerTail by norm_num [bm12884, scalar12884])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12884, bm12884, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12884 :
    agent12884.root+dsL+scalar12884.worldRadius < √(1/100/aL) ∧
    2*(agent12884.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12884, agent12884, scalar12884, tp12884, tm12884, ep12884, em12884, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12884, agent12884, scalar12884, tp12884, tm12884, ep12884, em12884, dsL]

noncomputable def master12884 : MasterCertificate 12884 world12884 agent12884 :=
  master scalar12884 dsL tp12884 tm12884 ep12884 em12884
    (by norm_num [dsL]) (by norm_num [tp12884]) (by norm_num [tm12884])
    (by norm_num [ep12884]) (by norm_num [em12884])
    positive12884 negative12884 tails12884.1 tails12884.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12884.1 tailGuards12884.2

theorem preserves12884 : master12884.toScalarCertificate = scalar12884 := rfl

noncomputable def tp12885 : ℝ := (1166506393 / 5000000000)
noncomputable def tm12885 : ℝ := (-((381213809 / 625000000)))
noncomputable def ep12885 : ℝ := (6489337739423711 / 12500000000000000000)
noncomputable def em12885 : ℝ := (3158426089289743 / 6250000000000000000)
noncomputable def bp12885 : ℝ := (21668765325276623189 / 50000000000000000000)
noncomputable def bm12885 : ℝ := (44311479870893555911 / 100000000000000000000)

theorem positive12885 :
    Eplus aL (agent12885.root+dsL) scalar12885.worldRadius world12885.frame
      agent12885.frame tp12885 ≤ -ep12885 := by
  apply positive_check (eT := (115646825665349002991 / 100000000000000000000)) (y := (37988914299256862327 / 100000000000000000000)) (u := (146212249392550434449 / 100000000000000000000))
  · norm_num [world12885, agent12885, scalar12885, tp12885, tm12885, ep12885, em12885, dsL]
  · norm_num [world12885, agent12885, scalar12885, tp12885, tm12885, ep12885, em12885, dsL]
  · norm_num [world12885, agent12885, scalar12885, tp12885, tm12885, ep12885, em12885, dsL]
  · norm_num [world12885, agent12885, scalar12885, tp12885, tm12885, ep12885, em12885, dsL]
  · norm_num [world12885, agent12885, scalar12885, tp12885, tm12885, ep12885, em12885, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12885, agent12885, tp12885, tm12885, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12885, agent12885, scalar12885, tp12885, tm12885, ep12885, em12885, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12885, agent12885, tp12885, tm12885, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12885, agent12885, scalar12885, tp12885, tm12885, ep12885, em12885, dsL]

theorem negative12885 :
    Eminus aL (agent12885.root+dsL) scalar12885.worldRadius world12885.frame
      agent12885.frame tm12885 ≤ -em12885 := by
  apply negative_check (lo := (68382255201152453941 / 100000000000000000000)) (hi := (34191127600576226971 / 50000000000000000000))
    (y := (-((35829989043230996489 / 50000000000000000000)))) (u := (48841013727746822903 / 100000000000000000000))
  · norm_num [world12885, agent12885, scalar12885, tp12885, tm12885, ep12885, em12885, dsL]
  · norm_num [world12885, agent12885, scalar12885, tp12885, tm12885, ep12885, em12885, dsL]
  · norm_num [world12885, agent12885, scalar12885, tp12885, tm12885, ep12885, em12885, dsL]
  · norm_num [world12885, agent12885, scalar12885, tp12885, tm12885, ep12885, em12885, dsL]
  · norm_num [world12885, agent12885, scalar12885, tp12885, tm12885, ep12885, em12885, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12885, agent12885, tp12885, tm12885, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12885, agent12885, tp12885, tm12885, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12885, agent12885, scalar12885, tp12885, tm12885, ep12885, em12885, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12885, agent12885, tp12885, tm12885, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12885, agent12885, scalar12885, tp12885, tm12885, ep12885, em12885, dsL]

theorem tails12885 :
    exp (-((12885:ℝ)*ep12885)) ≤ scalar12885.upperTail ∧
    exp (-((12885:ℝ)*em12885)) ≤ scalar12885.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12885:ℝ)) (by norm_num [ep12885]) ?_)
      (show bp12885^8 ≤ scalar12885.upperTail by norm_num [bp12885, scalar12885])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12885, bp12885, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12885:ℝ)) (by norm_num [em12885]) ?_)
      (show bm12885^8 ≤ scalar12885.lowerTail by norm_num [bm12885, scalar12885])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12885, bm12885, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12885 :
    agent12885.root+dsL+scalar12885.worldRadius < √(1/100/aL) ∧
    2*(agent12885.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12885, agent12885, scalar12885, tp12885, tm12885, ep12885, em12885, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12885, agent12885, scalar12885, tp12885, tm12885, ep12885, em12885, dsL]

noncomputable def master12885 : MasterCertificate 12885 world12885 agent12885 :=
  master scalar12885 dsL tp12885 tm12885 ep12885 em12885
    (by norm_num [dsL]) (by norm_num [tp12885]) (by norm_num [tm12885])
    (by norm_num [ep12885]) (by norm_num [em12885])
    positive12885 negative12885 tails12885.1 tails12885.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12885.1 tailGuards12885.2

theorem preserves12885 : master12885.toScalarCertificate = scalar12885 := rfl

noncomputable def tp12886 : ℝ := (466618397 / 2000000000)
noncomputable def tm12886 : ℝ := (-((1219917999 / 2000000000)))
noncomputable def ep12886 : ℝ := (51917108204172593 / 100000000000000000000)
noncomputable def em12886 : ℝ := (789638606514179 / 1562500000000000000)
noncomputable def bp12886 : ℝ := (43333038832416783647 / 100000000000000000000)
noncomputable def bm12886 : ℝ := (11076803846344588427 / 25000000000000000000)

theorem positive12886 :
    Eplus aL (agent12886.root+dsL) scalar12886.worldRadius world12886.frame
      agent12886.frame tp12886 ≤ -ep12886 := by
  apply positive_check (eT := (57823516859643011161 / 50000000000000000000)) (y := (37989638662443793271 / 100000000000000000000)) (u := (146213308504095720187 / 100000000000000000000))
  · norm_num [world12886, agent12886, scalar12886, tp12886, tm12886, ep12886, em12886, dsL]
  · norm_num [world12886, agent12886, scalar12886, tp12886, tm12886, ep12886, em12886, dsL]
  · norm_num [world12886, agent12886, scalar12886, tp12886, tm12886, ep12886, em12886, dsL]
  · norm_num [world12886, agent12886, scalar12886, tp12886, tm12886, ep12886, em12886, dsL]
  · norm_num [world12886, agent12886, scalar12886, tp12886, tm12886, ep12886, em12886, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12886, agent12886, tp12886, tm12886, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12886, agent12886, scalar12886, tp12886, tm12886, ep12886, em12886, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12886, agent12886, tp12886, tm12886, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12886, agent12886, scalar12886, tp12886, tm12886, ep12886, em12886, dsL]

theorem negative12886 :
    Eminus aL (agent12886.root+dsL) scalar12886.worldRadius world12886.frame
      agent12886.frame tm12886 ≤ -em12886 := by
  apply negative_check (lo := (3419104775539797121 / 5000000000000000000)) (hi := (68382095510795942421 / 100000000000000000000))
    (y := (-((1791499294871623751 / 2500000000000000000)))) (u := (24420508400313347503 / 50000000000000000000))
  · norm_num [world12886, agent12886, scalar12886, tp12886, tm12886, ep12886, em12886, dsL]
  · norm_num [world12886, agent12886, scalar12886, tp12886, tm12886, ep12886, em12886, dsL]
  · norm_num [world12886, agent12886, scalar12886, tp12886, tm12886, ep12886, em12886, dsL]
  · norm_num [world12886, agent12886, scalar12886, tp12886, tm12886, ep12886, em12886, dsL]
  · norm_num [world12886, agent12886, scalar12886, tp12886, tm12886, ep12886, em12886, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12886, agent12886, tp12886, tm12886, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12886, agent12886, tp12886, tm12886, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12886, agent12886, scalar12886, tp12886, tm12886, ep12886, em12886, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12886, agent12886, tp12886, tm12886, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12886, agent12886, scalar12886, tp12886, tm12886, ep12886, em12886, dsL]

theorem tails12886 :
    exp (-((12886:ℝ)*ep12886)) ≤ scalar12886.upperTail ∧
    exp (-((12886:ℝ)*em12886)) ≤ scalar12886.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12886:ℝ)) (by norm_num [ep12886]) ?_)
      (show bp12886^8 ≤ scalar12886.upperTail by norm_num [bp12886, scalar12886])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12886, bp12886, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12886:ℝ)) (by norm_num [em12886]) ?_)
      (show bm12886^8 ≤ scalar12886.lowerTail by norm_num [bm12886, scalar12886])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12886, bm12886, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12886 :
    agent12886.root+dsL+scalar12886.worldRadius < √(1/100/aL) ∧
    2*(agent12886.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12886, agent12886, scalar12886, tp12886, tm12886, ep12886, em12886, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12886, agent12886, scalar12886, tp12886, tm12886, ep12886, em12886, dsL]

noncomputable def master12886 : MasterCertificate 12886 world12886 agent12886 :=
  master scalar12886 dsL tp12886 tm12886 ep12886 em12886
    (by norm_num [dsL]) (by norm_num [tp12886]) (by norm_num [tm12886])
    (by norm_num [ep12886]) (by norm_num [em12886])
    positive12886 negative12886 tails12886.1 tails12886.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12886.1 tailGuards12886.2

theorem preserves12886 : master12886.toScalarCertificate = scalar12886 := rfl

noncomputable def tp12887 : ℝ := (2333171157 / 10000000000)
noncomputable def tm12887 : ℝ := (-((762469871 / 1250000000)))
noncomputable def ep12887 : ℝ := (6489939172062577 / 12500000000000000000)
noncomputable def em12887 : ℝ := (5053892312264589 / 10000000000000000000)
noncomputable def bp12887 : ℝ := (21664273999221633911 / 50000000000000000000)
noncomputable def bm12887 : ℝ := (44302951855410591291 / 100000000000000000000)

theorem positive12887 :
    Eplus aL (agent12887.root+dsL) scalar12887.worldRadius world12887.frame
      agent12887.frame tp12887 ≤ -ep12887 := by
  apply positive_check (eT := (57823620805785446189 / 50000000000000000000)) (y := (37990363147054094427 / 100000000000000000000)) (u := (29242873560170252173 / 20000000000000000000))
  · norm_num [world12887, agent12887, scalar12887, tp12887, tm12887, ep12887, em12887, dsL]
  · norm_num [world12887, agent12887, scalar12887, tp12887, tm12887, ep12887, em12887, dsL]
  · norm_num [world12887, agent12887, scalar12887, tp12887, tm12887, ep12887, em12887, dsL]
  · norm_num [world12887, agent12887, scalar12887, tp12887, tm12887, ep12887, em12887, dsL]
  · norm_num [world12887, agent12887, scalar12887, tp12887, tm12887, ep12887, em12887, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12887, agent12887, tp12887, tm12887, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12887, agent12887, scalar12887, tp12887, tm12887, ep12887, em12887, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12887, agent12887, tp12887, tm12887, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12887, agent12887, scalar12887, tp12887, tm12887, ep12887, em12887, dsL]

theorem negative12887 :
    Eminus aL (agent12887.root+dsL) scalar12887.worldRadius world12887.frame
      agent12887.frame tm12887 ≤ -em12887 := by
  apply negative_check (lo := (68381936095878891519 / 100000000000000000000)) (hi := (6677923446863173 / 9765625000000000))
    (y := (-((17914991458272668199 / 25000000000000000000)))) (u := (48841019712417958167 / 100000000000000000000))
  · norm_num [world12887, agent12887, scalar12887, tp12887, tm12887, ep12887, em12887, dsL]
  · norm_num [world12887, agent12887, scalar12887, tp12887, tm12887, ep12887, em12887, dsL]
  · norm_num [world12887, agent12887, scalar12887, tp12887, tm12887, ep12887, em12887, dsL]
  · norm_num [world12887, agent12887, scalar12887, tp12887, tm12887, ep12887, em12887, dsL]
  · norm_num [world12887, agent12887, scalar12887, tp12887, tm12887, ep12887, em12887, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12887, agent12887, tp12887, tm12887, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12887, agent12887, tp12887, tm12887, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12887, agent12887, scalar12887, tp12887, tm12887, ep12887, em12887, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12887, agent12887, tp12887, tm12887, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12887, agent12887, scalar12887, tp12887, tm12887, ep12887, em12887, dsL]

theorem tails12887 :
    exp (-((12887:ℝ)*ep12887)) ≤ scalar12887.upperTail ∧
    exp (-((12887:ℝ)*em12887)) ≤ scalar12887.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12887:ℝ)) (by norm_num [ep12887]) ?_)
      (show bp12887^8 ≤ scalar12887.upperTail by norm_num [bp12887, scalar12887])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12887, bp12887, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12887:ℝ)) (by norm_num [em12887]) ?_)
      (show bm12887^8 ≤ scalar12887.lowerTail by norm_num [bm12887, scalar12887])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12887, bm12887, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12887 :
    agent12887.root+dsL+scalar12887.worldRadius < √(1/100/aL) ∧
    2*(agent12887.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12887, agent12887, scalar12887, tp12887, tm12887, ep12887, em12887, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12887, agent12887, scalar12887, tp12887, tm12887, ep12887, em12887, dsL]

noncomputable def master12887 : MasterCertificate 12887 world12887 agent12887 :=
  master scalar12887 dsL tp12887 tm12887 ep12887 em12887
    (by norm_num [dsL]) (by norm_num [tp12887]) (by norm_num [tm12887])
    (by norm_num [ep12887]) (by norm_num [em12887])
    positive12887 negative12887 tails12887.1 tails12887.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12887.1 tailGuards12887.2

theorem preserves12887 : master12887.toScalarCertificate = scalar12887 := rfl

noncomputable def tp12888 : ℝ := (1166625153 / 5000000000)
noncomputable def tm12888 : ℝ := (-((190622741 / 312500000)))
noncomputable def ep12888 : ℝ := (649023958034917 / 1250000000000000000)
noncomputable def em12888 : ℝ := (50540973693009703 / 100000000000000000000)
noncomputable def bp12888 : ℝ := (21662029349846345591 / 50000000000000000000)
noncomputable def bm12888 : ℝ := (44298689746874791351 / 100000000000000000000)

theorem positive12888 :
    Eplus aL (agent12888.root+dsL) scalar12888.worldRadius world12888.frame
      agent12888.frame tp12888 ≤ -ep12888 := by
  apply positive_check (eT := (1806991396422553063 / 1562500000000000000)) (y := (37991087565931073591 / 100000000000000000000)) (u := (36553856752292253461 / 25000000000000000000))
  · norm_num [world12888, agent12888, scalar12888, tp12888, tm12888, ep12888, em12888, dsL]
  · norm_num [world12888, agent12888, scalar12888, tp12888, tm12888, ep12888, em12888, dsL]
  · norm_num [world12888, agent12888, scalar12888, tp12888, tm12888, ep12888, em12888, dsL]
  · norm_num [world12888, agent12888, scalar12888, tp12888, tm12888, ep12888, em12888, dsL]
  · norm_num [world12888, agent12888, scalar12888, tp12888, tm12888, ep12888, em12888, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12888, agent12888, tp12888, tm12888, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12888, agent12888, scalar12888, tp12888, tm12888, ep12888, em12888, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12888, agent12888, tp12888, tm12888, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12888, agent12888, scalar12888, tp12888, tm12888, ep12888, em12888, dsL]

theorem negative12888 :
    Eminus aL (agent12888.root+dsL) scalar12888.worldRadius world12888.frame
      agent12888.frame tm12888 ≤ -em12888 := by
  apply negative_check (lo := (17095444399930818313 / 25000000000000000000)) (hi := (68381777599723273253 / 100000000000000000000))
    (y := (-((3582997901725029357 / 5000000000000000000)))) (u := (24420511760664513857 / 50000000000000000000))
  · norm_num [world12888, agent12888, scalar12888, tp12888, tm12888, ep12888, em12888, dsL]
  · norm_num [world12888, agent12888, scalar12888, tp12888, tm12888, ep12888, em12888, dsL]
  · norm_num [world12888, agent12888, scalar12888, tp12888, tm12888, ep12888, em12888, dsL]
  · norm_num [world12888, agent12888, scalar12888, tp12888, tm12888, ep12888, em12888, dsL]
  · norm_num [world12888, agent12888, scalar12888, tp12888, tm12888, ep12888, em12888, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12888, agent12888, tp12888, tm12888, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12888, agent12888, tp12888, tm12888, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12888, agent12888, scalar12888, tp12888, tm12888, ep12888, em12888, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12888, agent12888, tp12888, tm12888, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12888, agent12888, scalar12888, tp12888, tm12888, ep12888, em12888, dsL]

theorem tails12888 :
    exp (-((12888:ℝ)*ep12888)) ≤ scalar12888.upperTail ∧
    exp (-((12888:ℝ)*em12888)) ≤ scalar12888.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12888:ℝ)) (by norm_num [ep12888]) ?_)
      (show bp12888^8 ≤ scalar12888.upperTail by norm_num [bp12888, scalar12888])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12888, bp12888, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12888:ℝ)) (by norm_num [em12888]) ?_)
      (show bm12888^8 ≤ scalar12888.lowerTail by norm_num [bm12888, scalar12888])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12888, bm12888, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12888 :
    agent12888.root+dsL+scalar12888.worldRadius < √(1/100/aL) ∧
    2*(agent12888.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12888, agent12888, scalar12888, tp12888, tm12888, ep12888, em12888, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12888, agent12888, scalar12888, tp12888, tm12888, ep12888, em12888, dsL]

noncomputable def master12888 : MasterCertificate 12888 world12888 agent12888 :=
  master scalar12888 dsL tp12888 tm12888 ep12888 em12888
    (by norm_num [dsL]) (by norm_num [tp12888]) (by norm_num [tm12888])
    (by norm_num [ep12888]) (by norm_num [em12888])
    positive12888 negative12888 tails12888.1 tails12888.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12888.1 tailGuards12888.2

theorem preserves12888 : master12888.toScalarCertificate = scalar12888 := rfl

noncomputable def tp12889 : ℝ := (2333329381 / 10000000000)
noncomputable def tm12889 : ℝ := (-((6100096337 / 10000000000)))
noncomputable def ep12889 : ℝ := (51924319719390001 / 100000000000000000000)
noncomputable def em12889 : ℝ := (2021720963834857 / 4000000000000000000)
noncomputable def bp12889 : ℝ := (21659784869102576639 / 50000000000000000000)
noncomputable def bm12889 : ℝ := (44294427940833519447 / 100000000000000000000)

theorem positive12889 :
    Eplus aL (agent12889.root+dsL) scalar12889.worldRadius world12889.frame
      agent12889.frame tp12889 ≤ -ep12889 := by
  apply positive_check (eT := (115647656630269920551 / 100000000000000000000)) (y := (18995905440062979389 / 50000000000000000000)) (u := (73108242304966283383 / 50000000000000000000))
  · norm_num [world12889, agent12889, scalar12889, tp12889, tm12889, ep12889, em12889, dsL]
  · norm_num [world12889, agent12889, scalar12889, tp12889, tm12889, ep12889, em12889, dsL]
  · norm_num [world12889, agent12889, scalar12889, tp12889, tm12889, ep12889, em12889, dsL]
  · norm_num [world12889, agent12889, scalar12889, tp12889, tm12889, ep12889, em12889, dsL]
  · norm_num [world12889, agent12889, scalar12889, tp12889, tm12889, ep12889, em12889, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12889, agent12889, tp12889, tm12889, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12889, agent12889, scalar12889, tp12889, tm12889, ep12889, em12889, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12889, agent12889, tp12889, tm12889, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12889, agent12889, scalar12889, tp12889, tm12889, ep12889, em12889, dsL]

theorem negative12889 :
    Eminus aL (agent12889.root+dsL) scalar12889.worldRadius world12889.frame
      agent12889.frame tm12889 ≤ -em12889 := by
  apply negative_check (lo := (6838161955355415703 / 10000000000000000000)) (hi := (68381619553554157031 / 100000000000000000000))
    (y := (-((71659949848055337193 / 100000000000000000000)))) (u := (24420513759836420731 / 50000000000000000000))
  · norm_num [world12889, agent12889, scalar12889, tp12889, tm12889, ep12889, em12889, dsL]
  · norm_num [world12889, agent12889, scalar12889, tp12889, tm12889, ep12889, em12889, dsL]
  · norm_num [world12889, agent12889, scalar12889, tp12889, tm12889, ep12889, em12889, dsL]
  · norm_num [world12889, agent12889, scalar12889, tp12889, tm12889, ep12889, em12889, dsL]
  · norm_num [world12889, agent12889, scalar12889, tp12889, tm12889, ep12889, em12889, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12889, agent12889, tp12889, tm12889, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12889, agent12889, tp12889, tm12889, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12889, agent12889, scalar12889, tp12889, tm12889, ep12889, em12889, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12889, agent12889, tp12889, tm12889, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12889, agent12889, scalar12889, tp12889, tm12889, ep12889, em12889, dsL]

theorem tails12889 :
    exp (-((12889:ℝ)*ep12889)) ≤ scalar12889.upperTail ∧
    exp (-((12889:ℝ)*em12889)) ≤ scalar12889.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12889:ℝ)) (by norm_num [ep12889]) ?_)
      (show bp12889^8 ≤ scalar12889.upperTail by norm_num [bp12889, scalar12889])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12889, bp12889, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12889:ℝ)) (by norm_num [em12889]) ?_)
      (show bm12889^8 ≤ scalar12889.lowerTail by norm_num [bm12889, scalar12889])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12889, bm12889, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12889 :
    agent12889.root+dsL+scalar12889.worldRadius < √(1/100/aL) ∧
    2*(agent12889.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12889, agent12889, scalar12889, tp12889, tm12889, ep12889, em12889, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12889, agent12889, scalar12889, tp12889, tm12889, ep12889, em12889, dsL]

noncomputable def master12889 : MasterCertificate 12889 world12889 agent12889 :=
  master scalar12889 dsL tp12889 tm12889 ep12889 em12889
    (by norm_num [dsL]) (by norm_num [tp12889]) (by norm_num [tm12889])
    (by norm_num [ep12889]) (by norm_num [em12889])
    positive12889 negative12889 tails12889.1 tails12889.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12889.1 tailGuards12889.2

theorem preserves12889 : master12889.toScalarCertificate = scalar12889 := rfl

noncomputable def tp12890 : ℝ := (2333481189 / 10000000000)
noncomputable def tm12890 : ℝ := (-((6100485379 / 10000000000)))
noncomputable def ep12890 : ℝ := (5192810338816177 / 10000000000000000000)
noncomputable def em12890 : ℝ := (1263664512706357 / 2500000000000000000)
noncomputable def bp12890 : ℝ := (21657058728693147787 / 50000000000000000000)
noncomputable def bm12890 : ℝ := (44289091604308237001 / 100000000000000000000)

theorem positive12890 :
    Eplus aL (agent12890.root+dsL) scalar12890.worldRadius world12890.frame
      agent12890.frame tp12890 ≤ -ep12890 := by
  apply positive_check (eT := (57824193992517590809 / 50000000000000000000)) (y := (37991814692276323989 / 100000000000000000000)) (u := (73108245091962462533 / 50000000000000000000))
  · norm_num [world12890, agent12890, scalar12890, tp12890, tm12890, ep12890, em12890, dsL]
  · norm_num [world12890, agent12890, scalar12890, tp12890, tm12890, ep12890, em12890, dsL]
  · norm_num [world12890, agent12890, scalar12890, tp12890, tm12890, ep12890, em12890, dsL]
  · norm_num [world12890, agent12890, scalar12890, tp12890, tm12890, ep12890, em12890, dsL]
  · norm_num [world12890, agent12890, scalar12890, tp12890, tm12890, ep12890, em12890, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12890, agent12890, tp12890, tm12890, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12890, agent12890, scalar12890, tp12890, tm12890, ep12890, em12890, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12890, agent12890, tp12890, tm12890, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12890, agent12890, scalar12890, tp12890, tm12890, ep12890, em12890, dsL]

theorem negative12890 :
    Eminus aL (agent12890.root+dsL) scalar12890.worldRadius world12890.frame
      agent12890.frame tm12890 ≤ -em12890 := by
  apply negative_check (lo := (13676104477989514279 / 20000000000000000000)) (hi := (17095130597486892849 / 25000000000000000000))
    (y := (-((35829029412189679829 / 50000000000000000000)))) (u := (4884195112379958801 / 10000000000000000000))
  · norm_num [world12890, agent12890, scalar12890, tp12890, tm12890, ep12890, em12890, dsL]
  · norm_num [world12890, agent12890, scalar12890, tp12890, tm12890, ep12890, em12890, dsL]
  · norm_num [world12890, agent12890, scalar12890, tp12890, tm12890, ep12890, em12890, dsL]
  · norm_num [world12890, agent12890, scalar12890, tp12890, tm12890, ep12890, em12890, dsL]
  · norm_num [world12890, agent12890, scalar12890, tp12890, tm12890, ep12890, em12890, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12890, agent12890, tp12890, tm12890, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12890, agent12890, tp12890, tm12890, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12890, agent12890, scalar12890, tp12890, tm12890, ep12890, em12890, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12890, agent12890, tp12890, tm12890, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12890, agent12890, scalar12890, tp12890, tm12890, ep12890, em12890, dsL]

theorem tails12890 :
    exp (-((12890:ℝ)*ep12890)) ≤ scalar12890.upperTail ∧
    exp (-((12890:ℝ)*em12890)) ≤ scalar12890.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12890:ℝ)) (by norm_num [ep12890]) ?_)
      (show bp12890^8 ≤ scalar12890.upperTail by norm_num [bp12890, scalar12890])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12890, bp12890, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12890:ℝ)) (by norm_num [em12890]) ?_)
      (show bm12890^8 ≤ scalar12890.lowerTail by norm_num [bm12890, scalar12890])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12890, bm12890, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12890 :
    agent12890.root+dsL+scalar12890.worldRadius < √(1/100/aL) ∧
    2*(agent12890.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12890, agent12890, scalar12890, tp12890, tm12890, ep12890, em12890, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12890, agent12890, scalar12890, tp12890, tm12890, ep12890, em12890, dsL]

noncomputable def master12890 : MasterCertificate 12890 world12890 agent12890 :=
  master scalar12890 dsL tp12890 tm12890 ep12890 em12890
    (by norm_num [dsL]) (by norm_num [tp12890]) (by norm_num [tm12890])
    (by norm_num [ep12890]) (by norm_num [em12890])
    positive12890 negative12890 tails12890.1 tails12890.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12890.1 tailGuards12890.2

theorem preserves12890 : master12890.toScalarCertificate = scalar12890 := rfl

noncomputable def tp12891 : ℝ := (2333560219 / 10000000000)
noncomputable def tm12891 : ℝ := (-((762581747 / 1250000000)))
noncomputable def ep12891 : ℝ := (12982625882758821 / 25000000000000000000)
noncomputable def em12891 : ℝ := (505486281788297 / 1000000000000000000)
noncomputable def bp12891 : ℝ := (4330963097821197281 / 10000000000000000000)
noncomputable def bm12891 : ℝ := (1771393285361472633 / 4000000000000000000)

theorem positive12891 :
    Eplus aL (agent12891.root+dsL) scalar12891.worldRadius world12891.frame
      agent12891.frame tp12891 ≤ -ep12891 := by
  apply positive_check (eT := (5782429748775362173 / 5000000000000000000)) (y := (3799253807456244241 / 10000000000000000000)) (u := (146217547891939931257 / 100000000000000000000))
  · norm_num [world12891, agent12891, scalar12891, tp12891, tm12891, ep12891, em12891, dsL]
  · norm_num [world12891, agent12891, scalar12891, tp12891, tm12891, ep12891, em12891, dsL]
  · norm_num [world12891, agent12891, scalar12891, tp12891, tm12891, ep12891, em12891, dsL]
  · norm_num [world12891, agent12891, scalar12891, tp12891, tm12891, ep12891, em12891, dsL]
  · norm_num [world12891, agent12891, scalar12891, tp12891, tm12891, ep12891, em12891, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12891, agent12891, tp12891, tm12891, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12891, agent12891, scalar12891, tp12891, tm12891, ep12891, em12891, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12891, agent12891, tp12891, tm12891, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12891, agent12891, scalar12891, tp12891, tm12891, ep12891, em12891, dsL]

theorem negative12891 :
    Eminus aL (agent12891.root+dsL) scalar12891.worldRadius world12891.frame
      agent12891.frame tm12891 ≤ -em12891 := by
  apply negative_check (lo := (17095091092897537963 / 25000000000000000000)) (hi := (68380364371590151853 / 100000000000000000000))
    (y := (-((14331610345516593189 / 20000000000000000000)))) (u := (24420977295006768489 / 50000000000000000000))
  · norm_num [world12891, agent12891, scalar12891, tp12891, tm12891, ep12891, em12891, dsL]
  · norm_num [world12891, agent12891, scalar12891, tp12891, tm12891, ep12891, em12891, dsL]
  · norm_num [world12891, agent12891, scalar12891, tp12891, tm12891, ep12891, em12891, dsL]
  · norm_num [world12891, agent12891, scalar12891, tp12891, tm12891, ep12891, em12891, dsL]
  · norm_num [world12891, agent12891, scalar12891, tp12891, tm12891, ep12891, em12891, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12891, agent12891, tp12891, tm12891, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12891, agent12891, tp12891, tm12891, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12891, agent12891, scalar12891, tp12891, tm12891, ep12891, em12891, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12891, agent12891, tp12891, tm12891, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12891, agent12891, scalar12891, tp12891, tm12891, ep12891, em12891, dsL]

theorem tails12891 :
    exp (-((12891:ℝ)*ep12891)) ≤ scalar12891.upperTail ∧
    exp (-((12891:ℝ)*em12891)) ≤ scalar12891.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12891:ℝ)) (by norm_num [ep12891]) ?_)
      (show bp12891^8 ≤ scalar12891.upperTail by norm_num [bp12891, scalar12891])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12891, bp12891, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12891:ℝ)) (by norm_num [em12891]) ?_)
      (show bm12891^8 ≤ scalar12891.lowerTail by norm_num [bm12891, scalar12891])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12891, bm12891, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12891 :
    agent12891.root+dsL+scalar12891.worldRadius < √(1/100/aL) ∧
    2*(agent12891.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12891, agent12891, scalar12891, tp12891, tm12891, ep12891, em12891, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12891, agent12891, scalar12891, tp12891, tm12891, ep12891, em12891, dsL]

noncomputable def master12891 : MasterCertificate 12891 world12891 agent12891 :=
  master scalar12891 dsL tp12891 tm12891 ep12891 em12891
    (by norm_num [dsL]) (by norm_num [tp12891]) (by norm_num [tm12891])
    (by norm_num [ep12891]) (by norm_num [em12891])
    positive12891 negative12891 tails12891.1 tails12891.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12891.1 tailGuards12891.2

theorem preserves12891 : master12891.toScalarCertificate = scalar12891 := rfl

noncomputable def tp12892 : ℝ := (2333639179 / 10000000000)
noncomputable def tm12892 : ℝ := (-((6100822413 / 10000000000)))
noncomputable def ep12892 : ℝ := (51932902072984821 / 100000000000000000000)
noncomputable def em12892 : ℝ := (50550674374096243 / 100000000000000000000)
noncomputable def bp12892 : ℝ := (10826286455281449861 / 25000000000000000000)
noncomputable def bm12892 : ℝ := (22140286949744865151 / 50000000000000000000)

theorem positive12892 :
    Eplus aL (agent12892.root+dsL) scalar12892.worldRadius world12892.frame
      agent12892.frame tp12892 ≤ -ep12892 := by
  apply positive_check (eT := (14456100186819426567 / 12500000000000000000)) (y := (118728939279456991 / 312500000000000000)) (u := (146218604310029695717 / 100000000000000000000))
  · norm_num [world12892, agent12892, scalar12892, tp12892, tm12892, ep12892, em12892, dsL]
  · norm_num [world12892, agent12892, scalar12892, tp12892, tm12892, ep12892, em12892, dsL]
  · norm_num [world12892, agent12892, scalar12892, tp12892, tm12892, ep12892, em12892, dsL]
  · norm_num [world12892, agent12892, scalar12892, tp12892, tm12892, ep12892, em12892, dsL]
  · norm_num [world12892, agent12892, scalar12892, tp12892, tm12892, ep12892, em12892, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12892, agent12892, tp12892, tm12892, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12892, agent12892, scalar12892, tp12892, tm12892, ep12892, em12892, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12892, agent12892, tp12892, tm12892, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12892, agent12892, scalar12892, tp12892, tm12892, ep12892, em12892, dsL]

theorem negative12892 :
    Eminus aL (agent12892.root+dsL) scalar12892.worldRadius world12892.frame
      agent12892.frame tm12892 ≤ -em12892 := by
  apply negative_check (lo := (34190103488957018057 / 50000000000000000000)) (hi := (13676041395582807223 / 20000000000000000000))
    (y := (-((35829021731358748723 / 50000000000000000000)))) (u := (48841958626735542843 / 100000000000000000000))
  · norm_num [world12892, agent12892, scalar12892, tp12892, tm12892, ep12892, em12892, dsL]
  · norm_num [world12892, agent12892, scalar12892, tp12892, tm12892, ep12892, em12892, dsL]
  · norm_num [world12892, agent12892, scalar12892, tp12892, tm12892, ep12892, em12892, dsL]
  · norm_num [world12892, agent12892, scalar12892, tp12892, tm12892, ep12892, em12892, dsL]
  · norm_num [world12892, agent12892, scalar12892, tp12892, tm12892, ep12892, em12892, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12892, agent12892, tp12892, tm12892, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12892, agent12892, tp12892, tm12892, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12892, agent12892, scalar12892, tp12892, tm12892, ep12892, em12892, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12892, agent12892, tp12892, tm12892, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12892, agent12892, scalar12892, tp12892, tm12892, ep12892, em12892, dsL]

theorem tails12892 :
    exp (-((12892:ℝ)*ep12892)) ≤ scalar12892.upperTail ∧
    exp (-((12892:ℝ)*em12892)) ≤ scalar12892.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12892:ℝ)) (by norm_num [ep12892]) ?_)
      (show bp12892^8 ≤ scalar12892.upperTail by norm_num [bp12892, scalar12892])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12892, bp12892, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12892:ℝ)) (by norm_num [em12892]) ?_)
      (show bm12892^8 ≤ scalar12892.lowerTail by norm_num [bm12892, scalar12892])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12892, bm12892, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12892 :
    agent12892.root+dsL+scalar12892.worldRadius < √(1/100/aL) ∧
    2*(agent12892.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12892, agent12892, scalar12892, tp12892, tm12892, ep12892, em12892, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12892, agent12892, scalar12892, tp12892, tm12892, ep12892, em12892, dsL]

noncomputable def master12892 : MasterCertificate 12892 world12892 agent12892 :=
  master scalar12892 dsL tp12892 tm12892 ep12892 em12892
    (by norm_num [dsL]) (by norm_num [tp12892]) (by norm_num [tm12892])
    (by norm_num [ep12892]) (by norm_num [em12892])
    positive12892 negative12892 tails12892.1 tails12892.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12892.1 tailGuards12892.2

theorem preserves12892 : master12892.toScalarCertificate = scalar12892 := rfl

noncomputable def tp12893 : ℝ := (2333718117 / 10000000000)
noncomputable def tm12893 : ℝ := (-((6100990887 / 10000000000)))
noncomputable def ep12893 : ℝ := (51935299811817773 / 100000000000000000000)
noncomputable def em12893 : ℝ := (3159544988543957 / 6250000000000000000)
noncomputable def bp12893 : ℝ := (21650330714663945691 / 50000000000000000000)
noncomputable def bm12893 : ℝ := (4427631638497461743 / 10000000000000000000)

theorem positive12893 :
    Eplus aL (agent12893.root+dsL) scalar12893.worldRadius world12893.frame
      agent12893.frame tp12893 ≤ -ep12893 := by
  apply positive_check (eT := (115649007888049949961 / 100000000000000000000)) (y := (9498495767534691171 / 25000000000000000000)) (u := (5848786429772162061 / 4000000000000000000))
  · norm_num [world12893, agent12893, scalar12893, tp12893, tm12893, ep12893, em12893, dsL]
  · norm_num [world12893, agent12893, scalar12893, tp12893, tm12893, ep12893, em12893, dsL]
  · norm_num [world12893, agent12893, scalar12893, tp12893, tm12893, ep12893, em12893, dsL]
  · norm_num [world12893, agent12893, scalar12893, tp12893, tm12893, ep12893, em12893, dsL]
  · norm_num [world12893, agent12893, scalar12893, tp12893, tm12893, ep12893, em12893, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12893, agent12893, tp12893, tm12893, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12893, agent12893, scalar12893, tp12893, tm12893, ep12893, em12893, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12893, agent12893, tp12893, tm12893, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12893, agent12893, scalar12893, tp12893, tm12893, ep12893, em12893, dsL]

theorem negative12893 :
    Eminus aL (agent12893.root+dsL) scalar12893.worldRadius world12893.frame
      agent12893.frame tm12893 ≤ -em12893 := by
  apply negative_check (lo := (17095012342408548501 / 25000000000000000000)) (hi := (13676009873926838801 / 20000000000000000000))
    (y := (-((71658036474169354649 / 100000000000000000000)))) (u := (48841962040079454629 / 100000000000000000000))
  · norm_num [world12893, agent12893, scalar12893, tp12893, tm12893, ep12893, em12893, dsL]
  · norm_num [world12893, agent12893, scalar12893, tp12893, tm12893, ep12893, em12893, dsL]
  · norm_num [world12893, agent12893, scalar12893, tp12893, tm12893, ep12893, em12893, dsL]
  · norm_num [world12893, agent12893, scalar12893, tp12893, tm12893, ep12893, em12893, dsL]
  · norm_num [world12893, agent12893, scalar12893, tp12893, tm12893, ep12893, em12893, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12893, agent12893, tp12893, tm12893, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12893, agent12893, tp12893, tm12893, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12893, agent12893, scalar12893, tp12893, tm12893, ep12893, em12893, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12893, agent12893, tp12893, tm12893, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12893, agent12893, scalar12893, tp12893, tm12893, ep12893, em12893, dsL]

theorem tails12893 :
    exp (-((12893:ℝ)*ep12893)) ≤ scalar12893.upperTail ∧
    exp (-((12893:ℝ)*em12893)) ≤ scalar12893.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12893:ℝ)) (by norm_num [ep12893]) ?_)
      (show bp12893^8 ≤ scalar12893.upperTail by norm_num [bp12893, scalar12893])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12893, bp12893, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12893:ℝ)) (by norm_num [em12893]) ?_)
      (show bm12893^8 ≤ scalar12893.lowerTail by norm_num [bm12893, scalar12893])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12893, bm12893, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12893 :
    agent12893.root+dsL+scalar12893.worldRadius < √(1/100/aL) ∧
    2*(agent12893.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12893, agent12893, scalar12893, tp12893, tm12893, ep12893, em12893, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12893, agent12893, scalar12893, tp12893, tm12893, ep12893, em12893, dsL]

noncomputable def master12893 : MasterCertificate 12893 world12893 agent12893 :=
  master scalar12893 dsL tp12893 tm12893 ep12893 em12893
    (by norm_num [dsL]) (by norm_num [tp12893]) (by norm_num [tm12893])
    (by norm_num [ep12893]) (by norm_num [em12893])
    positive12893 negative12893 tails12893.1 tails12893.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12893.1 tailGuards12893.2

theorem preserves12893 : master12893.toScalarCertificate = scalar12893 := rfl

noncomputable def tp12894 : ℝ := (466759399 / 2000000000)
noncomputable def tm12894 : ℝ := (-((6101159213 / 10000000000)))
noncomputable def ep12894 : ℝ := (51937696254963481 / 100000000000000000000)
noncomputable def em12894 : ℝ := (12638691011027843 / 25000000000000000000)
noncomputable def bp12894 : ℝ := (4329617814653577909 / 10000000000000000000)
noncomputable def bm12894 : ℝ := (44272059920534839869 / 100000000000000000000)

theorem positive12894 :
    Eplus aL (agent12894.root+dsL) scalar12894.worldRadius world12894.frame
      agent12894.frame tp12894 ≤ -ep12894 := by
  apply positive_check (eT := (23129842776439819157 / 20000000000000000000)) (y := (37994704859088202699 / 100000000000000000000)) (u := (29244143229093217913 / 20000000000000000000))
  · norm_num [world12894, agent12894, scalar12894, tp12894, tm12894, ep12894, em12894, dsL]
  · norm_num [world12894, agent12894, scalar12894, tp12894, tm12894, ep12894, em12894, dsL]
  · norm_num [world12894, agent12894, scalar12894, tp12894, tm12894, ep12894, em12894, dsL]
  · norm_num [world12894, agent12894, scalar12894, tp12894, tm12894, ep12894, em12894, dsL]
  · norm_num [world12894, agent12894, scalar12894, tp12894, tm12894, ep12894, em12894, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12894, agent12894, tp12894, tm12894, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12894, agent12894, scalar12894, tp12894, tm12894, ep12894, em12894, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12894, agent12894, tp12894, tm12894, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12894, agent12894, scalar12894, tp12894, tm12894, ep12894, em12894, dsL]

theorem negative12894 :
    Eminus aL (agent12894.root+dsL) scalar12894.worldRadius world12894.frame
      agent12894.frame tm12894 ≤ -em12894 := by
  apply negative_check (lo := (68379892334886671401 / 100000000000000000000)) (hi := (34189946167443335701 / 50000000000000000000))
    (y := (-((35829014218067429181 / 50000000000000000000)))) (u := (24420982983006684929 / 50000000000000000000))
  · norm_num [world12894, agent12894, scalar12894, tp12894, tm12894, ep12894, em12894, dsL]
  · norm_num [world12894, agent12894, scalar12894, tp12894, tm12894, ep12894, em12894, dsL]
  · norm_num [world12894, agent12894, scalar12894, tp12894, tm12894, ep12894, em12894, dsL]
  · norm_num [world12894, agent12894, scalar12894, tp12894, tm12894, ep12894, em12894, dsL]
  · norm_num [world12894, agent12894, scalar12894, tp12894, tm12894, ep12894, em12894, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12894, agent12894, tp12894, tm12894, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12894, agent12894, tp12894, tm12894, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12894, agent12894, scalar12894, tp12894, tm12894, ep12894, em12894, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12894, agent12894, tp12894, tm12894, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12894, agent12894, scalar12894, tp12894, tm12894, ep12894, em12894, dsL]

theorem tails12894 :
    exp (-((12894:ℝ)*ep12894)) ≤ scalar12894.upperTail ∧
    exp (-((12894:ℝ)*em12894)) ≤ scalar12894.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12894:ℝ)) (by norm_num [ep12894]) ?_)
      (show bp12894^8 ≤ scalar12894.upperTail by norm_num [bp12894, scalar12894])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12894, bp12894, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12894:ℝ)) (by norm_num [em12894]) ?_)
      (show bm12894^8 ≤ scalar12894.lowerTail by norm_num [bm12894, scalar12894])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12894, bm12894, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12894 :
    agent12894.root+dsL+scalar12894.worldRadius < √(1/100/aL) ∧
    2*(agent12894.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12894, agent12894, scalar12894, tp12894, tm12894, ep12894, em12894, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12894, agent12894, scalar12894, tp12894, tm12894, ep12894, em12894, dsL]

noncomputable def master12894 : MasterCertificate 12894 world12894 agent12894 :=
  master scalar12894 dsL tp12894 tm12894 ep12894 em12894
    (by norm_num [dsL]) (by norm_num [tp12894]) (by norm_num [tm12894])
    (by norm_num [ep12894]) (by norm_num [em12894])
    positive12894 negative12894 tails12894.1 tails12894.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12894.1 tailGuards12894.2

theorem preserves12894 : master12894.toScalarCertificate = scalar12894 := rfl

noncomputable def tp12895 : ℝ := (2333875859 / 10000000000)
noncomputable def tm12895 : ℝ := (-((1525331829 / 2500000000)))
noncomputable def ep12895 : ℝ := (25970045559689511 / 50000000000000000000)
noncomputable def em12895 : ℝ := (50556806822935423 / 100000000000000000000)
noncomputable def bp12895 : ℝ := (43291696170221112779 / 100000000000000000000)
noncomputable def bm12895 : ℝ := (4426780467267790537 / 10000000000000000000)

theorem positive12895 :
    Eplus aL (agent12895.root+dsL) scalar12895.worldRadius world12895.frame
      agent12895.frame tp12895 ≤ -ep12895 := by
  apply positive_check (eT := (115649419808418968417 / 100000000000000000000)) (y := (949885671044676543 / 2500000000000000000)) (u := (73110885918774880051 / 50000000000000000000))
  · norm_num [world12895, agent12895, scalar12895, tp12895, tm12895, ep12895, em12895, dsL]
  · norm_num [world12895, agent12895, scalar12895, tp12895, tm12895, ep12895, em12895, dsL]
  · norm_num [world12895, agent12895, scalar12895, tp12895, tm12895, ep12895, em12895, dsL]
  · norm_num [world12895, agent12895, scalar12895, tp12895, tm12895, ep12895, em12895, dsL]
  · norm_num [world12895, agent12895, scalar12895, tp12895, tm12895, ep12895, em12895, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12895, agent12895, tp12895, tm12895, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12895, agent12895, scalar12895, tp12895, tm12895, ep12895, em12895, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12895, agent12895, tp12895, tm12895, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12895, agent12895, scalar12895, tp12895, tm12895, ep12895, em12895, dsL]

theorem negative12895 :
    Eminus aL (agent12895.root+dsL) scalar12895.worldRadius world12895.frame
      agent12895.frame tm12895 ≤ -em12895 := by
  apply negative_check (lo := (13675947238629899923 / 20000000000000000000)) (hi := (2136866756035921863 / 3125000000000000000))
    (y := (-((71658019032736689289 / 100000000000000000000)))) (u := (9768394111763623837 / 20000000000000000000))
  · norm_num [world12895, agent12895, scalar12895, tp12895, tm12895, ep12895, em12895, dsL]
  · norm_num [world12895, agent12895, scalar12895, tp12895, tm12895, ep12895, em12895, dsL]
  · norm_num [world12895, agent12895, scalar12895, tp12895, tm12895, ep12895, em12895, dsL]
  · norm_num [world12895, agent12895, scalar12895, tp12895, tm12895, ep12895, em12895, dsL]
  · norm_num [world12895, agent12895, scalar12895, tp12895, tm12895, ep12895, em12895, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12895, agent12895, tp12895, tm12895, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12895, agent12895, tp12895, tm12895, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12895, agent12895, scalar12895, tp12895, tm12895, ep12895, em12895, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12895, agent12895, tp12895, tm12895, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12895, agent12895, scalar12895, tp12895, tm12895, ep12895, em12895, dsL]

theorem tails12895 :
    exp (-((12895:ℝ)*ep12895)) ≤ scalar12895.upperTail ∧
    exp (-((12895:ℝ)*em12895)) ≤ scalar12895.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12895:ℝ)) (by norm_num [ep12895]) ?_)
      (show bp12895^8 ≤ scalar12895.upperTail by norm_num [bp12895, scalar12895])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12895, bp12895, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12895:ℝ)) (by norm_num [em12895]) ?_)
      (show bm12895^8 ≤ scalar12895.lowerTail by norm_num [bm12895, scalar12895])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12895, bm12895, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12895 :
    agent12895.root+dsL+scalar12895.worldRadius < √(1/100/aL) ∧
    2*(agent12895.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12895, agent12895, scalar12895, tp12895, tm12895, ep12895, em12895, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12895, agent12895, scalar12895, tp12895, tm12895, ep12895, em12895, dsL]

noncomputable def master12895 : MasterCertificate 12895 world12895 agent12895 :=
  master scalar12895 dsL tp12895 tm12895 ep12895 em12895
    (by norm_num [dsL]) (by norm_num [tp12895]) (by norm_num [tm12895])
    (by norm_num [ep12895]) (by norm_num [em12895])
    positive12895 negative12895 tails12895.1 tails12895.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12895.1 tailGuards12895.2

theorem preserves12895 : master12895.toScalarCertificate = scalar12895 := rfl

noncomputable def tp12896 : ℝ := (2333954671 / 10000000000)
noncomputable def tm12896 : ℝ := (-((6101495437 / 10000000000)))
noncomputable def ep12896 : ℝ := (5194248533342123 / 10000000000000000000)
noncomputable def em12896 : ℝ := (12639712251712753 / 25000000000000000000)
noncomputable def bp12896 : ℝ := (10821803713133123349 / 25000000000000000000)
noncomputable def bm12896 : ℝ := (2766471877015646331 / 6250000000000000000)

theorem positive12896 :
    Eplus aL (agent12896.root+dsL) scalar12896.worldRadius world12896.frame
      agent12896.frame tp12896 ≤ -ep12896 := by
  apply positive_check (eT := (5782481269647609491 / 5000000000000000000)) (y := (759922963061474813 / 2000000000000000000)) (u := (9138926659718593843 / 6250000000000000000))
  · norm_num [world12896, agent12896, scalar12896, tp12896, tm12896, ep12896, em12896, dsL]
  · norm_num [world12896, agent12896, scalar12896, tp12896, tm12896, ep12896, em12896, dsL]
  · norm_num [world12896, agent12896, scalar12896, tp12896, tm12896, ep12896, em12896, dsL]
  · norm_num [world12896, agent12896, scalar12896, tp12896, tm12896, ep12896, em12896, dsL]
  · norm_num [world12896, agent12896, scalar12896, tp12896, tm12896, ep12896, em12896, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12896, agent12896, tp12896, tm12896, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12896, agent12896, scalar12896, tp12896, tm12896, ep12896, em12896, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12896, agent12896, tp12896, tm12896, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12896, agent12896, scalar12896, tp12896, tm12896, ep12896, em12896, dsL]

theorem negative12896 :
    Eminus aL (agent12896.root+dsL) scalar12896.worldRadius world12896.frame
      agent12896.frame tm12896 ≤ -em12896 := by
  apply negative_check (lo := (13675915983549971803 / 20000000000000000000)) (hi := (8547447489718732377 / 12500000000000000000))
    (y := (-((71658010434614561151 / 100000000000000000000)))) (u := (610524684478882227 / 1250000000000000000))
  · norm_num [world12896, agent12896, scalar12896, tp12896, tm12896, ep12896, em12896, dsL]
  · norm_num [world12896, agent12896, scalar12896, tp12896, tm12896, ep12896, em12896, dsL]
  · norm_num [world12896, agent12896, scalar12896, tp12896, tm12896, ep12896, em12896, dsL]
  · norm_num [world12896, agent12896, scalar12896, tp12896, tm12896, ep12896, em12896, dsL]
  · norm_num [world12896, agent12896, scalar12896, tp12896, tm12896, ep12896, em12896, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12896, agent12896, tp12896, tm12896, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12896, agent12896, tp12896, tm12896, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12896, agent12896, scalar12896, tp12896, tm12896, ep12896, em12896, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12896, agent12896, tp12896, tm12896, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12896, agent12896, scalar12896, tp12896, tm12896, ep12896, em12896, dsL]

theorem tails12896 :
    exp (-((12896:ℝ)*ep12896)) ≤ scalar12896.upperTail ∧
    exp (-((12896:ℝ)*em12896)) ≤ scalar12896.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12896:ℝ)) (by norm_num [ep12896]) ?_)
      (show bp12896^8 ≤ scalar12896.upperTail by norm_num [bp12896, scalar12896])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12896, bp12896, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12896:ℝ)) (by norm_num [em12896]) ?_)
      (show bm12896^8 ≤ scalar12896.lowerTail by norm_num [bm12896, scalar12896])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12896, bm12896, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12896 :
    agent12896.root+dsL+scalar12896.worldRadius < √(1/100/aL) ∧
    2*(agent12896.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12896, agent12896, scalar12896, tp12896, tm12896, ep12896, em12896, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12896, agent12896, scalar12896, tp12896, tm12896, ep12896, em12896, dsL]

noncomputable def master12896 : MasterCertificate 12896 world12896 agent12896 :=
  master scalar12896 dsL tp12896 tm12896 ep12896 em12896
    (by norm_num [dsL]) (by norm_num [tp12896]) (by norm_num [tm12896])
    (by norm_num [ep12896]) (by norm_num [em12896])
    positive12896 negative12896 tails12896.1 tails12896.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12896.1 tailGuards12896.2

theorem preserves12896 : master12896.toScalarCertificate = scalar12896 := rfl

noncomputable def tp12897 : ℝ := (583508369 / 2500000000)
noncomputable def tm12897 : ℝ := (-((6101663477 / 10000000000)))
noncomputable def ep12897 : ℝ := (51944877628661181 / 100000000000000000000)
noncomputable def em12897 : ℝ := (25280444691034367 / 50000000000000000000)
noncomputable def bp12897 : ℝ := (8656547015708183931 / 20000000000000000000)
noncomputable def bm12897 : ℝ := (22129648432655764501 / 50000000000000000000)

theorem positive12897 :
    Eplus aL (agent12897.root+dsL) scalar12897.worldRadius world12897.frame
      agent12897.frame tp12897 ≤ -ep12897 := by
  apply positive_check (eT := (2312996619200420561 / 2000000000000000000)) (y := (9499217470152664293 / 25000000000000000000)) (u := (36555970472427581107 / 25000000000000000000))
  · norm_num [world12897, agent12897, scalar12897, tp12897, tm12897, ep12897, em12897, dsL]
  · norm_num [world12897, agent12897, scalar12897, tp12897, tm12897, ep12897, em12897, dsL]
  · norm_num [world12897, agent12897, scalar12897, tp12897, tm12897, ep12897, em12897, dsL]
  · norm_num [world12897, agent12897, scalar12897, tp12897, tm12897, ep12897, em12897, dsL]
  · norm_num [world12897, agent12897, scalar12897, tp12897, tm12897, ep12897, em12897, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12897, agent12897, tp12897, tm12897, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12897, agent12897, scalar12897, tp12897, tm12897, ep12897, em12897, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12897, agent12897, tp12897, tm12897, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12897, agent12897, scalar12897, tp12897, tm12897, ep12897, em12897, dsL]

theorem negative12897 :
    Eminus aL (agent12897.root+dsL) scalar12897.worldRadius world12897.frame
      agent12897.frame tm12897 ≤ -em12897 := by
  apply negative_check (lo := (8547427991298852453 / 12500000000000000000)) (hi := (547035391443126557 / 800000000000000000))
    (y := (-((35829000796019236347 / 50000000000000000000)))) (u := (48841979077199550219 / 100000000000000000000))
  · norm_num [world12897, agent12897, scalar12897, tp12897, tm12897, ep12897, em12897, dsL]
  · norm_num [world12897, agent12897, scalar12897, tp12897, tm12897, ep12897, em12897, dsL]
  · norm_num [world12897, agent12897, scalar12897, tp12897, tm12897, ep12897, em12897, dsL]
  · norm_num [world12897, agent12897, scalar12897, tp12897, tm12897, ep12897, em12897, dsL]
  · norm_num [world12897, agent12897, scalar12897, tp12897, tm12897, ep12897, em12897, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12897, agent12897, tp12897, tm12897, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12897, agent12897, tp12897, tm12897, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12897, agent12897, scalar12897, tp12897, tm12897, ep12897, em12897, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12897, agent12897, tp12897, tm12897, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12897, agent12897, scalar12897, tp12897, tm12897, ep12897, em12897, dsL]

theorem tails12897 :
    exp (-((12897:ℝ)*ep12897)) ≤ scalar12897.upperTail ∧
    exp (-((12897:ℝ)*em12897)) ≤ scalar12897.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12897:ℝ)) (by norm_num [ep12897]) ?_)
      (show bp12897^8 ≤ scalar12897.upperTail by norm_num [bp12897, scalar12897])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12897, bp12897, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12897:ℝ)) (by norm_num [em12897]) ?_)
      (show bm12897^8 ≤ scalar12897.lowerTail by norm_num [bm12897, scalar12897])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12897, bm12897, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12897 :
    agent12897.root+dsL+scalar12897.worldRadius < √(1/100/aL) ∧
    2*(agent12897.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12897, agent12897, scalar12897, tp12897, tm12897, ep12897, em12897, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12897, agent12897, scalar12897, tp12897, tm12897, ep12897, em12897, dsL]

noncomputable def master12897 : MasterCertificate 12897 world12897 agent12897 :=
  master scalar12897 dsL tp12897 tm12897 ep12897 em12897
    (by norm_num [dsL]) (by norm_num [tp12897]) (by norm_num [tm12897])
    (by norm_num [ep12897]) (by norm_num [em12897])
    positive12897 negative12897 tails12897.1 tails12897.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12897.1 tailGuards12897.2

theorem preserves12897 : master12897.toScalarCertificate = scalar12897 := rfl

noncomputable def tp12898 : ℝ := (2334112161 / 10000000000)
noncomputable def tm12898 : ℝ := (-((6101831323 / 10000000000)))
noncomputable def ep12898 : ℝ := (51947268825166063 / 100000000000000000000)
noncomputable def em12898 : ℝ := (50562928752965453 / 100000000000000000000)
noncomputable def bp12898 : ℝ := (21639128137984812819 / 50000000000000000000)
noncomputable def bm12898 : ℝ := (22127522298945493403 / 50000000000000000000)

theorem positive12898 :
    Eplus aL (agent12898.root+dsL) scalar12898.worldRadius world12898.frame
      agent12898.frame tp12898 ≤ -ep12898 := by
  apply positive_check (eT := (57825017847754559473 / 50000000000000000000)) (y := (18998794949118622073 / 50000000000000000000)) (u := (146224934731224527753 / 100000000000000000000))
  · norm_num [world12898, agent12898, scalar12898, tp12898, tm12898, ep12898, em12898, dsL]
  · norm_num [world12898, agent12898, scalar12898, tp12898, tm12898, ep12898, em12898, dsL]
  · norm_num [world12898, agent12898, scalar12898, tp12898, tm12898, ep12898, em12898, dsL]
  · norm_num [world12898, agent12898, scalar12898, tp12898, tm12898, ep12898, em12898, dsL]
  · norm_num [world12898, agent12898, scalar12898, tp12898, tm12898, ep12898, em12898, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12898, agent12898, tp12898, tm12898, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12898, agent12898, scalar12898, tp12898, tm12898, ep12898, em12898, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12898, agent12898, tp12898, tm12898, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12898, agent12898, scalar12898, tp12898, tm12898, ep12898, em12898, dsL]

theorem negative12898 :
    Eminus aL (agent12898.root+dsL) scalar12898.worldRadius world12898.frame
      agent12898.frame tm12898 ≤ -em12898 := by
  apply negative_check (lo := (1367585374249045687 / 2000000000000000000)) (hi := (68379268712452284351 / 100000000000000000000))
    (y := (-((71657991791431335591 / 100000000000000000000)))) (u := (4884198386401027213 / 10000000000000000000))
  · norm_num [world12898, agent12898, scalar12898, tp12898, tm12898, ep12898, em12898, dsL]
  · norm_num [world12898, agent12898, scalar12898, tp12898, tm12898, ep12898, em12898, dsL]
  · norm_num [world12898, agent12898, scalar12898, tp12898, tm12898, ep12898, em12898, dsL]
  · norm_num [world12898, agent12898, scalar12898, tp12898, tm12898, ep12898, em12898, dsL]
  · norm_num [world12898, agent12898, scalar12898, tp12898, tm12898, ep12898, em12898, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12898, agent12898, tp12898, tm12898, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12898, agent12898, tp12898, tm12898, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12898, agent12898, scalar12898, tp12898, tm12898, ep12898, em12898, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12898, agent12898, tp12898, tm12898, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12898, agent12898, scalar12898, tp12898, tm12898, ep12898, em12898, dsL]

theorem tails12898 :
    exp (-((12898:ℝ)*ep12898)) ≤ scalar12898.upperTail ∧
    exp (-((12898:ℝ)*em12898)) ≤ scalar12898.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12898:ℝ)) (by norm_num [ep12898]) ?_)
      (show bp12898^8 ≤ scalar12898.upperTail by norm_num [bp12898, scalar12898])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12898, bp12898, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12898:ℝ)) (by norm_num [em12898]) ?_)
      (show bm12898^8 ≤ scalar12898.lowerTail by norm_num [bm12898, scalar12898])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12898, bm12898, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12898 :
    agent12898.root+dsL+scalar12898.worldRadius < √(1/100/aL) ∧
    2*(agent12898.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12898, agent12898, scalar12898, tp12898, tm12898, ep12898, em12898, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12898, agent12898, scalar12898, tp12898, tm12898, ep12898, em12898, dsL]

noncomputable def master12898 : MasterCertificate 12898 world12898 agent12898 :=
  master scalar12898 dsL tp12898 tm12898 ep12898 em12898
    (by norm_num [dsL]) (by norm_num [tp12898]) (by norm_num [tm12898])
    (by norm_num [ep12898]) (by norm_num [em12898])
    positive12898 negative12898 tails12898.1 tails12898.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12898.1 tailGuards12898.2

theorem preserves12898 : master12898.toScalarCertificate = scalar12898 := rfl

noncomputable def tp12899 : ℝ := (2334190919 / 10000000000)
noncomputable def tm12899 : ℝ := (-((6101999203 / 10000000000)))
noncomputable def ep12899 : ℝ := (51949658896129387 / 100000000000000000000)
noncomputable def em12899 : ℝ := (50564967089020003 / 100000000000000000000)
noncomputable def bp12899 : ℝ := (43273778463495131583 / 100000000000000000000)
noncomputable def bm12899 : ℝ := (22125396625875568279 / 50000000000000000000)

theorem positive12899 :
    Eplus aL (agent12899.root+dsL) scalar12899.worldRadius world12899.frame
      agent12899.frame tp12899 ≤ -ep12899 := by
  apply positive_check (eT := (115650240989878173551 / 100000000000000000000)) (y := (18999155739846428589 / 50000000000000000000)) (u := (18278248733380482269 / 12500000000000000000))
  · norm_num [world12899, agent12899, scalar12899, tp12899, tm12899, ep12899, em12899, dsL]
  · norm_num [world12899, agent12899, scalar12899, tp12899, tm12899, ep12899, em12899, dsL]
  · norm_num [world12899, agent12899, scalar12899, tp12899, tm12899, ep12899, em12899, dsL]
  · norm_num [world12899, agent12899, scalar12899, tp12899, tm12899, ep12899, em12899, dsL]
  · norm_num [world12899, agent12899, scalar12899, tp12899, tm12899, ep12899, em12899, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12899, agent12899, tp12899, tm12899, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12899, agent12899, scalar12899, tp12899, tm12899, ep12899, em12899, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12899, agent12899, tp12899, tm12899, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12899, agent12899, scalar12899, tp12899, tm12899, ep12899, em12899, dsL]

theorem negative12899 :
    Eminus aL (agent12899.root+dsL) scalar12899.worldRadius world12899.frame
      agent12899.frame tm12899 ≤ -em12899 := by
  apply negative_check (lo := (17094778323168661237 / 25000000000000000000)) (hi := (68379113292674644949 / 100000000000000000000))
    (y := (-((71657982821737232409 / 100000000000000000000)))) (u := (48841988244987015137 / 100000000000000000000))
  · norm_num [world12899, agent12899, scalar12899, tp12899, tm12899, ep12899, em12899, dsL]
  · norm_num [world12899, agent12899, scalar12899, tp12899, tm12899, ep12899, em12899, dsL]
  · norm_num [world12899, agent12899, scalar12899, tp12899, tm12899, ep12899, em12899, dsL]
  · norm_num [world12899, agent12899, scalar12899, tp12899, tm12899, ep12899, em12899, dsL]
  · norm_num [world12899, agent12899, scalar12899, tp12899, tm12899, ep12899, em12899, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12899, agent12899, tp12899, tm12899, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12899, agent12899, tp12899, tm12899, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12899, agent12899, scalar12899, tp12899, tm12899, ep12899, em12899, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12899, agent12899, tp12899, tm12899, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12899, agent12899, scalar12899, tp12899, tm12899, ep12899, em12899, dsL]

theorem tails12899 :
    exp (-((12899:ℝ)*ep12899)) ≤ scalar12899.upperTail ∧
    exp (-((12899:ℝ)*em12899)) ≤ scalar12899.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12899:ℝ)) (by norm_num [ep12899]) ?_)
      (show bp12899^8 ≤ scalar12899.upperTail by norm_num [bp12899, scalar12899])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12899, bp12899, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12899:ℝ)) (by norm_num [em12899]) ?_)
      (show bm12899^8 ≤ scalar12899.lowerTail by norm_num [bm12899, scalar12899])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12899, bm12899, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12899 :
    agent12899.root+dsL+scalar12899.worldRadius < √(1/100/aL) ∧
    2*(agent12899.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12899, agent12899, scalar12899, tp12899, tm12899, ep12899, em12899, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12899, agent12899, scalar12899, tp12899, tm12899, ep12899, em12899, dsL]

noncomputable def master12899 : MasterCertificate 12899 world12899 agent12899 :=
  master scalar12899 dsL tp12899 tm12899 ep12899 em12899
    (by norm_num [dsL]) (by norm_num [tp12899]) (by norm_num [tm12899])
    (by norm_num [ep12899]) (by norm_num [em12899])
    positive12899 negative12899 tails12899.1 tails12899.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12899.1 tailGuards12899.2

theorem preserves12899 : master12899.toScalarCertificate = scalar12899 := rfl

end BstLean.Part268
