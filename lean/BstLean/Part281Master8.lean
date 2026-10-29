import BstLean.Part261Checker
import BstLean.Part281Scalar8
namespace BstLean.Part281
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12059 : ℝ := (2363863967 / 10000000000)
noncomputable def tm12059 : ℝ := (-((764833767 / 1250000000)))
noncomputable def ep12059 : ℝ := (10866041660711019 / 20000000000000000000)
noncomputable def em12059 : ℝ := (52408203276895867 / 100000000000000000000)
noncomputable def bp12059 : ℝ := (11022248791297537609 / 25000000000000000000)
noncomputable def bm12059 : ℝ := (22692508574689329287 / 50000000000000000000)

theorem positive12059 :
    Eplus aL (agent12059.root+dsL) scalar12059.worldRadius world12059.frame
      agent12059.frame tp12059 ≤ -ep12059 := by
  apply positive_check (eT := (116195199899634190813 / 100000000000000000000)) (y := (39568660850167188697 / 100000000000000000000)) (u := (148540373169877703781 / 100000000000000000000))
  · norm_num [world12059, agent12059, scalar12059, tp12059, tm12059, ep12059, em12059, dsL]
  · norm_num [world12059, agent12059, scalar12059, tp12059, tm12059, ep12059, em12059, dsL]
  · norm_num [world12059, agent12059, scalar12059, tp12059, tm12059, ep12059, em12059, dsL]
  · norm_num [world12059, agent12059, scalar12059, tp12059, tm12059, ep12059, em12059, dsL]
  · norm_num [world12059, agent12059, scalar12059, tp12059, tm12059, ep12059, em12059, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12059, agent12059, tp12059, tm12059, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12059, agent12059, scalar12059, tp12059, tm12059, ep12059, em12059, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12059, agent12059, tp12059, tm12059, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12059, agent12059, scalar12059, tp12059, tm12059, ep12059, em12059, dsL]

theorem negative12059 :
    Eminus aL (agent12059.root+dsL) scalar12059.worldRadius world12059.frame
      agent12059.frame tm12059 ≤ -em12059 := by
  apply negative_check (lo := (8475701974833040441 / 12500000000000000000)) (hi := (67805615798664323529 / 100000000000000000000))
    (y := (-((73338497053365671237 / 100000000000000000000)))) (u := (12007012502727068307 / 25000000000000000000))
  · norm_num [world12059, agent12059, scalar12059, tp12059, tm12059, ep12059, em12059, dsL]
  · norm_num [world12059, agent12059, scalar12059, tp12059, tm12059, ep12059, em12059, dsL]
  · norm_num [world12059, agent12059, scalar12059, tp12059, tm12059, ep12059, em12059, dsL]
  · norm_num [world12059, agent12059, scalar12059, tp12059, tm12059, ep12059, em12059, dsL]
  · norm_num [world12059, agent12059, scalar12059, tp12059, tm12059, ep12059, em12059, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12059, agent12059, tp12059, tm12059, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12059, agent12059, tp12059, tm12059, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12059, agent12059, scalar12059, tp12059, tm12059, ep12059, em12059, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12059, agent12059, tp12059, tm12059, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12059, agent12059, scalar12059, tp12059, tm12059, ep12059, em12059, dsL]

theorem tails12059 :
    exp (-((12059:ℝ)*ep12059)) ≤ scalar12059.upperTail ∧
    exp (-((12059:ℝ)*em12059)) ≤ scalar12059.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12059:ℝ)) (by norm_num [ep12059]) ?_)
      (show bp12059^8 ≤ scalar12059.upperTail by norm_num [bp12059, scalar12059])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12059, bp12059, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12059:ℝ)) (by norm_num [em12059]) ?_)
      (show bm12059^8 ≤ scalar12059.lowerTail by norm_num [bm12059, scalar12059])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12059, bm12059, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12059 :
    agent12059.root+dsL+scalar12059.worldRadius < √(1/100/aL) ∧
    2*(agent12059.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12059, agent12059, scalar12059, tp12059, tm12059, ep12059, em12059, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12059, agent12059, scalar12059, tp12059, tm12059, ep12059, em12059, dsL]

noncomputable def master12059 : MasterCertificate 12059 world12059 agent12059 :=
  master scalar12059 dsL tp12059 tm12059 ep12059 em12059
    (by norm_num [dsL]) (by norm_num [tp12059]) (by norm_num [tm12059])
    (by norm_num [ep12059]) (by norm_num [em12059])
    positive12059 negative12059 tails12059.1 tails12059.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12059.1 tailGuards12059.2

theorem preserves12059 : master12059.toScalarCertificate = scalar12059 := rfl

noncomputable def tp12060 : ℝ := (472793331 / 2000000000)
noncomputable def tm12060 : ℝ := (-((6118900953 / 10000000000)))
noncomputable def ep12060 : ℝ := (1086664680256033 / 2000000000000000000)
noncomputable def em12060 : ℝ := (52410840250493471 / 100000000000000000000)
noncomputable def bp12060 : ℝ := (22041995115841846823 / 50000000000000000000)
noncomputable def bm12060 : ℝ := (2269012002724555169 / 5000000000000000000)

theorem positive12060 :
    Eplus aL (agent12060.root+dsL) scalar12060.worldRadius world12060.frame
      agent12060.frame tp12060 ≤ -ep12060 := by
  apply positive_check (eT := (11619553476316934863 / 10000000000000000000)) (y := (9892330143165649999 / 25000000000000000000)) (u := (742706765636833849 / 500000000000000000))
  · norm_num [world12060, agent12060, scalar12060, tp12060, tm12060, ep12060, em12060, dsL]
  · norm_num [world12060, agent12060, scalar12060, tp12060, tm12060, ep12060, em12060, dsL]
  · norm_num [world12060, agent12060, scalar12060, tp12060, tm12060, ep12060, em12060, dsL]
  · norm_num [world12060, agent12060, scalar12060, tp12060, tm12060, ep12060, em12060, dsL]
  · norm_num [world12060, agent12060, scalar12060, tp12060, tm12060, ep12060, em12060, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12060, agent12060, tp12060, tm12060, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12060, agent12060, scalar12060, tp12060, tm12060, ep12060, em12060, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12060, agent12060, tp12060, tm12060, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12060, agent12060, scalar12060, tp12060, tm12060, ep12060, em12060, dsL]

theorem negative12060 :
    Eminus aL (agent12060.root+dsL) scalar12060.worldRadius world12060.frame
      agent12060.frame tm12060 ≤ -em12060 := by
  apply negative_check (lo := (847565757678546151 / 1250000000000000000)) (hi := (67805260614283692081 / 100000000000000000000))
    (y := (-((18334530318577487359 / 25000000000000000000)))) (u := (24014115245300094021 / 50000000000000000000))
  · norm_num [world12060, agent12060, scalar12060, tp12060, tm12060, ep12060, em12060, dsL]
  · norm_num [world12060, agent12060, scalar12060, tp12060, tm12060, ep12060, em12060, dsL]
  · norm_num [world12060, agent12060, scalar12060, tp12060, tm12060, ep12060, em12060, dsL]
  · norm_num [world12060, agent12060, scalar12060, tp12060, tm12060, ep12060, em12060, dsL]
  · norm_num [world12060, agent12060, scalar12060, tp12060, tm12060, ep12060, em12060, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12060, agent12060, tp12060, tm12060, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12060, agent12060, tp12060, tm12060, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12060, agent12060, scalar12060, tp12060, tm12060, ep12060, em12060, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12060, agent12060, tp12060, tm12060, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12060, agent12060, scalar12060, tp12060, tm12060, ep12060, em12060, dsL]

theorem tails12060 :
    exp (-((12060:ℝ)*ep12060)) ≤ scalar12060.upperTail ∧
    exp (-((12060:ℝ)*em12060)) ≤ scalar12060.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12060:ℝ)) (by norm_num [ep12060]) ?_)
      (show bp12060^8 ≤ scalar12060.upperTail by norm_num [bp12060, scalar12060])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12060, bp12060, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12060:ℝ)) (by norm_num [em12060]) ?_)
      (show bm12060^8 ≤ scalar12060.lowerTail by norm_num [bm12060, scalar12060])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12060, bm12060, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12060 :
    agent12060.root+dsL+scalar12060.worldRadius < √(1/100/aL) ∧
    2*(agent12060.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12060, agent12060, scalar12060, tp12060, tm12060, ep12060, em12060, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12060, agent12060, scalar12060, tp12060, tm12060, ep12060, em12060, dsL]

noncomputable def master12060 : MasterCertificate 12060 world12060 agent12060 :=
  master scalar12060 dsL tp12060 tm12060 ep12060 em12060
    (by norm_num [dsL]) (by norm_num [tp12060]) (by norm_num [tm12060])
    (by norm_num [ep12060]) (by norm_num [em12060])
    positive12060 negative12060 tails12060.1 tails12060.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12060.1 tailGuards12060.2

theorem preserves12060 : master12060.toScalarCertificate = scalar12060 := rfl

noncomputable def tp12061 : ℝ := (1182034603 / 5000000000)
noncomputable def tm12061 : ℝ := (-((3059565939 / 5000000000)))
noncomputable def ep12061 : ℝ := (54336257681049921 / 100000000000000000000)
noncomputable def em12061 : ℝ := (6551684416954567 / 12500000000000000000)
noncomputable def bp12061 : ℝ := (1377468340288846371 / 3125000000000000000)
noncomputable def bm12061 : ℝ := (45375464455168246691 / 100000000000000000000)

theorem positive12061 :
    Eplus aL (agent12061.root+dsL) scalar12061.worldRadius world12061.frame
      agent12061.frame tp12061 ≤ -ep12061 := by
  apply positive_check (eT := (5809793432620662227 / 5000000000000000000)) (y := (39569978425255464111 / 100000000000000000000)) (u := (74271165156862006497 / 50000000000000000000))
  · norm_num [world12061, agent12061, scalar12061, tp12061, tm12061, ep12061, em12061, dsL]
  · norm_num [world12061, agent12061, scalar12061, tp12061, tm12061, ep12061, em12061, dsL]
  · norm_num [world12061, agent12061, scalar12061, tp12061, tm12061, ep12061, em12061, dsL]
  · norm_num [world12061, agent12061, scalar12061, tp12061, tm12061, ep12061, em12061, dsL]
  · norm_num [world12061, agent12061, scalar12061, tp12061, tm12061, ep12061, em12061, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12061, agent12061, tp12061, tm12061, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12061, agent12061, scalar12061, tp12061, tm12061, ep12061, em12061, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12061, agent12061, tp12061, tm12061, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12061, agent12061, scalar12061, tp12061, tm12061, ep12061, em12061, dsL]

theorem negative12061 :
    Eminus aL (agent12061.root+dsL) scalar12061.worldRadius world12061.frame
      agent12061.frame tm12061 ≤ -em12061 := by
  apply negative_check (lo := (13560980981170096043 / 20000000000000000000)) (hi := (8475613113231310027 / 12500000000000000000))
    (y := (-((7333774741223577219 / 10000000000000000000)))) (u := (48028410050274543381 / 100000000000000000000))
  · norm_num [world12061, agent12061, scalar12061, tp12061, tm12061, ep12061, em12061, dsL]
  · norm_num [world12061, agent12061, scalar12061, tp12061, tm12061, ep12061, em12061, dsL]
  · norm_num [world12061, agent12061, scalar12061, tp12061, tm12061, ep12061, em12061, dsL]
  · norm_num [world12061, agent12061, scalar12061, tp12061, tm12061, ep12061, em12061, dsL]
  · norm_num [world12061, agent12061, scalar12061, tp12061, tm12061, ep12061, em12061, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12061, agent12061, tp12061, tm12061, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12061, agent12061, tp12061, tm12061, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12061, agent12061, scalar12061, tp12061, tm12061, ep12061, em12061, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12061, agent12061, tp12061, tm12061, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12061, agent12061, scalar12061, tp12061, tm12061, ep12061, em12061, dsL]

theorem tails12061 :
    exp (-((12061:ℝ)*ep12061)) ≤ scalar12061.upperTail ∧
    exp (-((12061:ℝ)*em12061)) ≤ scalar12061.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12061:ℝ)) (by norm_num [ep12061]) ?_)
      (show bp12061^8 ≤ scalar12061.upperTail by norm_num [bp12061, scalar12061])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12061, bp12061, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12061:ℝ)) (by norm_num [em12061]) ?_)
      (show bm12061^8 ≤ scalar12061.lowerTail by norm_num [bm12061, scalar12061])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12061, bm12061, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12061 :
    agent12061.root+dsL+scalar12061.worldRadius < √(1/100/aL) ∧
    2*(agent12061.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12061, agent12061, scalar12061, tp12061, tm12061, ep12061, em12061, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12061, agent12061, scalar12061, tp12061, tm12061, ep12061, em12061, dsL]

noncomputable def master12061 : MasterCertificate 12061 world12061 agent12061 :=
  master scalar12061 dsL tp12061 tm12061 ep12061 em12061
    (by norm_num [dsL]) (by norm_num [tp12061]) (by norm_num [tm12061])
    (by norm_num [ep12061]) (by norm_num [em12061])
    positive12061 negative12061 tails12061.1 tails12061.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12061.1 tailGuards12061.2

theorem preserves12061 : master12061.toScalarCertificate = scalar12061 := rfl

noncomputable def tp12062 : ℝ := (236417177 / 1000000000)
noncomputable def tm12062 : ℝ := (-((6119362627 / 10000000000)))
noncomputable def ep12062 : ℝ := (2173571190008197 / 4000000000000000000)
noncomputable def em12062 : ℝ := (10483221789762879 / 20000000000000000000)
noncomputable def bp12062 : ℝ := (44073984844135711543 / 100000000000000000000)
noncomputable def bm12062 : ℝ := (11342672516613612827 / 25000000000000000000)

theorem positive12062 :
    Eplus aL (agent12062.root+dsL) scalar12062.worldRadius world12062.frame
      agent12062.frame tp12062 ≤ -ep12062 := by
  apply positive_check (eT := (116196202674071665303 / 100000000000000000000)) (y := (39570637166644558489 / 100000000000000000000)) (u := (148543308826757046413 / 100000000000000000000))
  · norm_num [world12062, agent12062, scalar12062, tp12062, tm12062, ep12062, em12062, dsL]
  · norm_num [world12062, agent12062, scalar12062, tp12062, tm12062, ep12062, em12062, dsL]
  · norm_num [world12062, agent12062, scalar12062, tp12062, tm12062, ep12062, em12062, dsL]
  · norm_num [world12062, agent12062, scalar12062, tp12062, tm12062, ep12062, em12062, dsL]
  · norm_num [world12062, agent12062, scalar12062, tp12062, tm12062, ep12062, em12062, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12062, agent12062, tp12062, tm12062, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12062, agent12062, scalar12062, tp12062, tm12062, ep12062, em12062, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12062, agent12062, tp12062, tm12062, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12062, agent12062, scalar12062, tp12062, tm12062, ep12062, em12062, dsL]

theorem negative12062 :
    Eminus aL (agent12062.root+dsL) scalar12062.worldRadius world12062.frame
      agent12062.frame tm12062 ≤ -em12062 := by
  apply negative_check (lo := (8475568737012693359 / 12500000000000000000)) (hi := (67804549896101546873 / 100000000000000000000))
    (y := (-((458358582698716589 / 625000000000000000)))) (u := (48028589763527357147 / 100000000000000000000))
  · norm_num [world12062, agent12062, scalar12062, tp12062, tm12062, ep12062, em12062, dsL]
  · norm_num [world12062, agent12062, scalar12062, tp12062, tm12062, ep12062, em12062, dsL]
  · norm_num [world12062, agent12062, scalar12062, tp12062, tm12062, ep12062, em12062, dsL]
  · norm_num [world12062, agent12062, scalar12062, tp12062, tm12062, ep12062, em12062, dsL]
  · norm_num [world12062, agent12062, scalar12062, tp12062, tm12062, ep12062, em12062, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12062, agent12062, tp12062, tm12062, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12062, agent12062, tp12062, tm12062, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12062, agent12062, scalar12062, tp12062, tm12062, ep12062, em12062, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12062, agent12062, tp12062, tm12062, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12062, agent12062, scalar12062, tp12062, tm12062, ep12062, em12062, dsL]

theorem tails12062 :
    exp (-((12062:ℝ)*ep12062)) ≤ scalar12062.upperTail ∧
    exp (-((12062:ℝ)*em12062)) ≤ scalar12062.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12062:ℝ)) (by norm_num [ep12062]) ?_)
      (show bp12062^8 ≤ scalar12062.upperTail by norm_num [bp12062, scalar12062])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12062, bp12062, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12062:ℝ)) (by norm_num [em12062]) ?_)
      (show bm12062^8 ≤ scalar12062.lowerTail by norm_num [bm12062, scalar12062])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12062, bm12062, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12062 :
    agent12062.root+dsL+scalar12062.worldRadius < √(1/100/aL) ∧
    2*(agent12062.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12062, agent12062, scalar12062, tp12062, tm12062, ep12062, em12062, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12062, agent12062, scalar12062, tp12062, tm12062, ep12062, em12062, dsL]

noncomputable def master12062 : MasterCertificate 12062 world12062 agent12062 :=
  master scalar12062 dsL tp12062 tm12062 ep12062 em12062
    (by norm_num [dsL]) (by norm_num [tp12062]) (by norm_num [tm12062])
    (by norm_num [ep12062]) (by norm_num [em12062])
    positive12062 negative12062 tails12062.1 tails12062.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12062.1 tailGuards12062.2

theorem preserves12062 : master12062.toScalarCertificate = scalar12062 := rfl

noncomputable def tp12063 : ℝ := (1182137139 / 5000000000)
noncomputable def tm12063 : ℝ := (-((6119593069 / 10000000000)))
noncomputable def ep12063 : ℝ := (27171149999315397 / 50000000000000000000)
noncomputable def em12063 : ℝ := (2096749633226917 / 4000000000000000000)
noncomputable def bp12063 : ℝ := (44068984243591236283 / 100000000000000000000)
noncomputable def bm12063 : ℝ := (22682958532868933183 / 50000000000000000000)

theorem positive12063 :
    Eplus aL (agent12063.root+dsL) scalar12063.worldRadius world12063.frame
      agent12063.frame tp12063 ≤ -ep12063 := by
  apply positive_check (eT := (23239307263819202143 / 20000000000000000000)) (y := (19785647829298595191 / 50000000000000000000)) (u := (37136071743928089073 / 25000000000000000000))
  · norm_num [world12063, agent12063, scalar12063, tp12063, tm12063, ep12063, em12063, dsL]
  · norm_num [world12063, agent12063, scalar12063, tp12063, tm12063, ep12063, em12063, dsL]
  · norm_num [world12063, agent12063, scalar12063, tp12063, tm12063, ep12063, em12063, dsL]
  · norm_num [world12063, agent12063, scalar12063, tp12063, tm12063, ep12063, em12063, dsL]
  · norm_num [world12063, agent12063, scalar12063, tp12063, tm12063, ep12063, em12063, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12063, agent12063, tp12063, tm12063, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12063, agent12063, scalar12063, tp12063, tm12063, ep12063, em12063, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12063, agent12063, tp12063, tm12063, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12063, agent12063, scalar12063, tp12063, tm12063, ep12063, em12063, dsL]

theorem negative12063 :
    Eminus aL (agent12063.root+dsL) scalar12063.worldRadius world12063.frame
      agent12063.frame tm12063 ≤ -em12063 := by
  apply negative_check (lo := (16951049037229490593 / 25000000000000000000)) (hi := (67804196148917962373 / 100000000000000000000))
    (y := (-((73336997197112218837 / 100000000000000000000)))) (u := (24014385184010960093 / 50000000000000000000))
  · norm_num [world12063, agent12063, scalar12063, tp12063, tm12063, ep12063, em12063, dsL]
  · norm_num [world12063, agent12063, scalar12063, tp12063, tm12063, ep12063, em12063, dsL]
  · norm_num [world12063, agent12063, scalar12063, tp12063, tm12063, ep12063, em12063, dsL]
  · norm_num [world12063, agent12063, scalar12063, tp12063, tm12063, ep12063, em12063, dsL]
  · norm_num [world12063, agent12063, scalar12063, tp12063, tm12063, ep12063, em12063, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12063, agent12063, tp12063, tm12063, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12063, agent12063, tp12063, tm12063, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12063, agent12063, scalar12063, tp12063, tm12063, ep12063, em12063, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12063, agent12063, tp12063, tm12063, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12063, agent12063, scalar12063, tp12063, tm12063, ep12063, em12063, dsL]

theorem tails12063 :
    exp (-((12063:ℝ)*ep12063)) ≤ scalar12063.upperTail ∧
    exp (-((12063:ℝ)*em12063)) ≤ scalar12063.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12063:ℝ)) (by norm_num [ep12063]) ?_)
      (show bp12063^8 ≤ scalar12063.upperTail by norm_num [bp12063, scalar12063])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12063, bp12063, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12063:ℝ)) (by norm_num [em12063]) ?_)
      (show bm12063^8 ≤ scalar12063.lowerTail by norm_num [bm12063, scalar12063])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12063, bm12063, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12063 :
    agent12063.root+dsL+scalar12063.worldRadius < √(1/100/aL) ∧
    2*(agent12063.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12063, agent12063, scalar12063, tp12063, tm12063, ep12063, em12063, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12063, agent12063, scalar12063, tp12063, tm12063, ep12063, em12063, dsL]

noncomputable def master12063 : MasterCertificate 12063 world12063 agent12063 :=
  master scalar12063 dsL tp12063 tm12063 ep12063 em12063
    (by norm_num [dsL]) (by norm_num [tp12063]) (by norm_num [tm12063])
    (by norm_num [ep12063]) (by norm_num [em12063])
    positive12063 negative12063 tails12063.1 tails12063.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12063.1 tailGuards12063.2

theorem preserves12063 : master12063.toScalarCertificate = scalar12063 := rfl

noncomputable def tp12064 : ℝ := (2364376699 / 10000000000)
noncomputable def tm12064 : ℝ := (-((6119823717 / 10000000000)))
noncomputable def ep12064 : ℝ := (5434531901963903 / 10000000000000000000)
noncomputable def em12064 : ℝ := (26210685777332681 / 50000000000000000000)
noncomputable def bp12064 : ℝ := (44063984693301082777 / 100000000000000000000)
noncomputable def bm12064 : ℝ := (45361145060712198423 / 100000000000000000000)

theorem positive12064 :
    Eplus aL (agent12064.root+dsL) scalar12064.worldRadius world12064.frame
      agent12064.frame tp12064 ≤ -ep12064 := by
  apply positive_check (eT := (116196869358795273483 / 100000000000000000000)) (y := (316575625898072523 / 800000000000000000)) (u := (148545263774458549473 / 100000000000000000000))
  · norm_num [world12064, agent12064, scalar12064, tp12064, tm12064, ep12064, em12064, dsL]
  · norm_num [world12064, agent12064, scalar12064, tp12064, tm12064, ep12064, em12064, dsL]
  · norm_num [world12064, agent12064, scalar12064, tp12064, tm12064, ep12064, em12064, dsL]
  · norm_num [world12064, agent12064, scalar12064, tp12064, tm12064, ep12064, em12064, dsL]
  · norm_num [world12064, agent12064, scalar12064, tp12064, tm12064, ep12064, em12064, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12064, agent12064, tp12064, tm12064, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12064, agent12064, scalar12064, tp12064, tm12064, ep12064, em12064, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12064, agent12064, tp12064, tm12064, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12064, agent12064, scalar12064, tp12064, tm12064, ep12064, em12064, dsL]

theorem negative12064 :
    Eminus aL (agent12064.root+dsL) scalar12064.worldRadius world12064.frame
      agent12064.frame tm12064 ≤ -em12064 := by
  apply negative_check (lo := (67803841455795668563 / 100000000000000000000)) (hi := (16950960363948917141 / 25000000000000000000))
    (y := (-((4583539037030026843 / 6250000000000000000)))) (u := (6003618665722288143 / 12500000000000000000))
  · norm_num [world12064, agent12064, scalar12064, tp12064, tm12064, ep12064, em12064, dsL]
  · norm_num [world12064, agent12064, scalar12064, tp12064, tm12064, ep12064, em12064, dsL]
  · norm_num [world12064, agent12064, scalar12064, tp12064, tm12064, ep12064, em12064, dsL]
  · norm_num [world12064, agent12064, scalar12064, tp12064, tm12064, ep12064, em12064, dsL]
  · norm_num [world12064, agent12064, scalar12064, tp12064, tm12064, ep12064, em12064, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12064, agent12064, tp12064, tm12064, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12064, agent12064, tp12064, tm12064, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12064, agent12064, scalar12064, tp12064, tm12064, ep12064, em12064, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12064, agent12064, tp12064, tm12064, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12064, agent12064, scalar12064, tp12064, tm12064, ep12064, em12064, dsL]

theorem tails12064 :
    exp (-((12064:ℝ)*ep12064)) ≤ scalar12064.upperTail ∧
    exp (-((12064:ℝ)*em12064)) ≤ scalar12064.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12064:ℝ)) (by norm_num [ep12064]) ?_)
      (show bp12064^8 ≤ scalar12064.upperTail by norm_num [bp12064, scalar12064])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12064, bp12064, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12064:ℝ)) (by norm_num [em12064]) ?_)
      (show bm12064^8 ≤ scalar12064.lowerTail by norm_num [bm12064, scalar12064])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12064, bm12064, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12064 :
    agent12064.root+dsL+scalar12064.worldRadius < √(1/100/aL) ∧
    2*(agent12064.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12064, agent12064, scalar12064, tp12064, tm12064, ep12064, em12064, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12064, agent12064, scalar12064, tp12064, tm12064, ep12064, em12064, dsL]

noncomputable def master12064 : MasterCertificate 12064 world12064 agent12064 :=
  master scalar12064 dsL tp12064 tm12064 ep12064 em12064
    (by norm_num [dsL]) (by norm_num [tp12064]) (by norm_num [tm12064])
    (by norm_num [ep12064]) (by norm_num [em12064])
    positive12064 negative12064 tails12064.1 tails12064.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12064.1 tailGuards12064.2

theorem preserves12064 : master12064.toScalarCertificate = scalar12064 := rfl

noncomputable def tp12065 : ℝ := (1182239527 / 5000000000)
noncomputable def tm12065 : ℝ := (-((3060026939 / 5000000000)))
noncomputable def ep12065 : ℝ := (54348335849147959 / 100000000000000000000)
noncomputable def em12065 : ℝ := (52424000234350673 / 100000000000000000000)
noncomputable def bp12065 : ℝ := (2753686677114841199 / 6250000000000000000)
noncomputable def bm12065 : ℝ := (45356374657718794041 / 100000000000000000000)

theorem positive12065 :
    Eplus aL (agent12065.root+dsL) scalar12065.worldRadius world12065.frame
      agent12065.frame tp12065 ≤ -ep12065 := by
  apply positive_check (eT := (2323944038962851489 / 2000000000000000000)) (y := (19786305192129694039 / 50000000000000000000)) (u := (9284139996150686083 / 6250000000000000000))
  · norm_num [world12065, agent12065, scalar12065, tp12065, tm12065, ep12065, em12065, dsL]
  · norm_num [world12065, agent12065, scalar12065, tp12065, tm12065, ep12065, em12065, dsL]
  · norm_num [world12065, agent12065, scalar12065, tp12065, tm12065, ep12065, em12065, dsL]
  · norm_num [world12065, agent12065, scalar12065, tp12065, tm12065, ep12065, em12065, dsL]
  · norm_num [world12065, agent12065, scalar12065, tp12065, tm12065, ep12065, em12065, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12065, agent12065, tp12065, tm12065, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12065, agent12065, scalar12065, tp12065, tm12065, ep12065, em12065, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12065, agent12065, tp12065, tm12065, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12065, agent12065, scalar12065, tp12065, tm12065, ep12065, em12065, dsL]

theorem negative12065 :
    Eminus aL (agent12065.root+dsL) scalar12065.worldRadius world12065.frame
      agent12065.frame tm12065 ≤ -em12065 := by
  apply negative_check (lo := (3390174440000724151 / 5000000000000000000)) (hi := (67803488800014483021 / 100000000000000000000))
    (y := (-((18334062090807236891 / 25000000000000000000)))) (u := (3001820626567173109 / 6250000000000000000))
  · norm_num [world12065, agent12065, scalar12065, tp12065, tm12065, ep12065, em12065, dsL]
  · norm_num [world12065, agent12065, scalar12065, tp12065, tm12065, ep12065, em12065, dsL]
  · norm_num [world12065, agent12065, scalar12065, tp12065, tm12065, ep12065, em12065, dsL]
  · norm_num [world12065, agent12065, scalar12065, tp12065, tm12065, ep12065, em12065, dsL]
  · norm_num [world12065, agent12065, scalar12065, tp12065, tm12065, ep12065, em12065, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12065, agent12065, tp12065, tm12065, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12065, agent12065, tp12065, tm12065, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12065, agent12065, scalar12065, tp12065, tm12065, ep12065, em12065, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12065, agent12065, tp12065, tm12065, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12065, agent12065, scalar12065, tp12065, tm12065, ep12065, em12065, dsL]

theorem tails12065 :
    exp (-((12065:ℝ)*ep12065)) ≤ scalar12065.upperTail ∧
    exp (-((12065:ℝ)*em12065)) ≤ scalar12065.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12065:ℝ)) (by norm_num [ep12065]) ?_)
      (show bp12065^8 ≤ scalar12065.upperTail by norm_num [bp12065, scalar12065])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12065, bp12065, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12065:ℝ)) (by norm_num [em12065]) ?_)
      (show bm12065^8 ≤ scalar12065.lowerTail by norm_num [bm12065, scalar12065])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12065, bm12065, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12065 :
    agent12065.root+dsL+scalar12065.worldRadius < √(1/100/aL) ∧
    2*(agent12065.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12065, agent12065, scalar12065, tp12065, tm12065, ep12065, em12065, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12065, agent12065, scalar12065, tp12065, tm12065, ep12065, em12065, dsL]

noncomputable def master12065 : MasterCertificate 12065 world12065 agent12065 :=
  master scalar12065 dsL tp12065 tm12065 ep12065 em12065
    (by norm_num [dsL]) (by norm_num [tp12065]) (by norm_num [tm12065])
    (by norm_num [ep12065]) (by norm_num [em12065])
    positive12065 negative12065 tails12065.1 tails12065.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12065.1 tailGuards12065.2

theorem preserves12065 : master12065.toScalarCertificate = scalar12065 := rfl

noncomputable def tp12066 : ℝ := (2364581439 / 10000000000)
noncomputable def tm12066 : ℝ := (-((6120284007 / 10000000000)))
noncomputable def ep12066 : ℝ := (54351350754410489 / 100000000000000000000)
noncomputable def em12066 : ℝ := (26213313580371031 / 50000000000000000000)
noncomputable def bp12066 : ℝ := (8810798097508209441 / 20000000000000000000)
noncomputable def bm12066 : ℝ := (22675802828823944373 / 50000000000000000000)

theorem positive12066 :
    Eplus aL (agent12066.root+dsL) scalar12066.worldRadius world12066.frame
      agent12066.frame tp12066 ≤ -ep12066 := by
  apply positive_check (eT := (116197534795297477669 / 100000000000000000000)) (y := (39573268616637091519 / 100000000000000000000)) (u := (148547217721076150501 / 100000000000000000000))
  · norm_num [world12066, agent12066, scalar12066, tp12066, tm12066, ep12066, em12066, dsL]
  · norm_num [world12066, agent12066, scalar12066, tp12066, tm12066, ep12066, em12066, dsL]
  · norm_num [world12066, agent12066, scalar12066, tp12066, tm12066, ep12066, em12066, dsL]
  · norm_num [world12066, agent12066, scalar12066, tp12066, tm12066, ep12066, em12066, dsL]
  · norm_num [world12066, agent12066, scalar12066, tp12066, tm12066, ep12066, em12066, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12066, agent12066, tp12066, tm12066, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12066, agent12066, scalar12066, tp12066, tm12066, ep12066, em12066, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12066, agent12066, tp12066, tm12066, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12066, agent12066, scalar12066, tp12066, tm12066, ep12066, em12066, dsL]

theorem negative12066 :
    Eminus aL (agent12066.root+dsL) scalar12066.worldRadius world12066.frame
      agent12066.frame tm12066 ≤ -em12066 := by
  apply negative_check (lo := (67803136222884940343 / 100000000000000000000)) (hi := (8475392027860617543 / 12500000000000000000))
    (y := (-((36667936399697112553 / 50000000000000000000)))) (u := (48029310405455997277 / 100000000000000000000))
  · norm_num [world12066, agent12066, scalar12066, tp12066, tm12066, ep12066, em12066, dsL]
  · norm_num [world12066, agent12066, scalar12066, tp12066, tm12066, ep12066, em12066, dsL]
  · norm_num [world12066, agent12066, scalar12066, tp12066, tm12066, ep12066, em12066, dsL]
  · norm_num [world12066, agent12066, scalar12066, tp12066, tm12066, ep12066, em12066, dsL]
  · norm_num [world12066, agent12066, scalar12066, tp12066, tm12066, ep12066, em12066, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12066, agent12066, tp12066, tm12066, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12066, agent12066, tp12066, tm12066, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12066, agent12066, scalar12066, tp12066, tm12066, ep12066, em12066, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12066, agent12066, tp12066, tm12066, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12066, agent12066, scalar12066, tp12066, tm12066, ep12066, em12066, dsL]

theorem tails12066 :
    exp (-((12066:ℝ)*ep12066)) ≤ scalar12066.upperTail ∧
    exp (-((12066:ℝ)*em12066)) ≤ scalar12066.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12066:ℝ)) (by norm_num [ep12066]) ?_)
      (show bp12066^8 ≤ scalar12066.upperTail by norm_num [bp12066, scalar12066])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12066, bp12066, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12066:ℝ)) (by norm_num [em12066]) ?_)
      (show bm12066^8 ≤ scalar12066.lowerTail by norm_num [bm12066, scalar12066])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12066, bm12066, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12066 :
    agent12066.root+dsL+scalar12066.worldRadius < √(1/100/aL) ∧
    2*(agent12066.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12066, agent12066, scalar12066, tp12066, tm12066, ep12066, em12066, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12066, agent12066, scalar12066, tp12066, tm12066, ep12066, em12066, dsL]

noncomputable def master12066 : MasterCertificate 12066 world12066 agent12066 :=
  master scalar12066 dsL tp12066 tm12066 ep12066 em12066
    (by norm_num [dsL]) (by norm_num [tp12066]) (by norm_num [tm12066])
    (by norm_num [ep12066]) (by norm_num [em12066])
    positive12066 negative12066 tails12066.1 tails12066.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12066.1 tailGuards12066.2

theorem preserves12066 : master12066.toScalarCertificate = scalar12066 := rfl

noncomputable def tp12067 : ℝ := (2364683677 / 10000000000)
noncomputable def tm12067 : ℝ := (-((6120514053 / 10000000000)))
noncomputable def ep12067 : ℝ := (10870872930580633 / 20000000000000000000)
noncomputable def em12067 : ℝ := (26214626543412699 / 50000000000000000000)
noncomputable def bp12067 : ℝ := (44048995044750004563 / 100000000000000000000)
noncomputable def bm12067 : ℝ := (11336709386354494823 / 25000000000000000000)

theorem positive12067 :
    Eplus aL (agent12067.root+dsL) scalar12067.worldRadius world12067.frame
      agent12067.frame tp12067 ≤ -ep12067 := by
  apply positive_check (eT := (14524733324324065933 / 12500000000000000000)) (y := (4946740626786913461 / 12500000000000000000)) (u := (148548192784734760929 / 100000000000000000000))
  · norm_num [world12067, agent12067, scalar12067, tp12067, tm12067, ep12067, em12067, dsL]
  · norm_num [world12067, agent12067, scalar12067, tp12067, tm12067, ep12067, em12067, dsL]
  · norm_num [world12067, agent12067, scalar12067, tp12067, tm12067, ep12067, em12067, dsL]
  · norm_num [world12067, agent12067, scalar12067, tp12067, tm12067, ep12067, em12067, dsL]
  · norm_num [world12067, agent12067, scalar12067, tp12067, tm12067, ep12067, em12067, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12067, agent12067, tp12067, tm12067, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12067, agent12067, scalar12067, tp12067, tm12067, ep12067, em12067, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12067, agent12067, tp12067, tm12067, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12067, agent12067, scalar12067, tp12067, tm12067, ep12067, em12067, dsL]

theorem negative12067 :
    Eminus aL (agent12067.root+dsL) scalar12067.worldRadius world12067.frame
      agent12067.frame tm12067 ≤ -em12067 := by
  apply negative_check (lo := (67802783943831429389 / 100000000000000000000)) (hi := (6780278394383142939 / 10000000000000000000))
    (y := (-((14667099625894369243 / 20000000000000000000)))) (u := (3001843147323320299 / 6250000000000000000))
  · norm_num [world12067, agent12067, scalar12067, tp12067, tm12067, ep12067, em12067, dsL]
  · norm_num [world12067, agent12067, scalar12067, tp12067, tm12067, ep12067, em12067, dsL]
  · norm_num [world12067, agent12067, scalar12067, tp12067, tm12067, ep12067, em12067, dsL]
  · norm_num [world12067, agent12067, scalar12067, tp12067, tm12067, ep12067, em12067, dsL]
  · norm_num [world12067, agent12067, scalar12067, tp12067, tm12067, ep12067, em12067, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12067, agent12067, tp12067, tm12067, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12067, agent12067, tp12067, tm12067, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12067, agent12067, scalar12067, tp12067, tm12067, ep12067, em12067, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12067, agent12067, tp12067, tm12067, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12067, agent12067, scalar12067, tp12067, tm12067, ep12067, em12067, dsL]

theorem tails12067 :
    exp (-((12067:ℝ)*ep12067)) ≤ scalar12067.upperTail ∧
    exp (-((12067:ℝ)*em12067)) ≤ scalar12067.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12067:ℝ)) (by norm_num [ep12067]) ?_)
      (show bp12067^8 ≤ scalar12067.upperTail by norm_num [bp12067, scalar12067])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12067, bp12067, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12067:ℝ)) (by norm_num [em12067]) ?_)
      (show bm12067^8 ≤ scalar12067.lowerTail by norm_num [bm12067, scalar12067])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12067, bm12067, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12067 :
    agent12067.root+dsL+scalar12067.worldRadius < √(1/100/aL) ∧
    2*(agent12067.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12067, agent12067, scalar12067, tp12067, tm12067, ep12067, em12067, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12067, agent12067, scalar12067, tp12067, tm12067, ep12067, em12067, dsL]

noncomputable def master12067 : MasterCertificate 12067 world12067 agent12067 :=
  master scalar12067 dsL tp12067 tm12067 ep12067 em12067
    (by norm_num [dsL]) (by norm_num [tp12067]) (by norm_num [tm12067])
    (by norm_num [ep12067]) (by norm_num [em12067])
    positive12067 negative12067 tails12067.1 tails12067.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12067.1 tailGuards12067.2

theorem preserves12067 : master12067.toScalarCertificate = scalar12067 := rfl

noncomputable def tp12068 : ℝ := (472957179 / 2000000000)
noncomputable def tm12068 : ℝ := (-((6120744017 / 10000000000)))
noncomputable def ep12068 : ℝ := (10871475399773513 / 20000000000000000000)
noncomputable def em12068 : ℝ := (52431877573745321 / 100000000000000000000)
noncomputable def bp12068 : ℝ := (1376375027126740407 / 3125000000000000000)
noncomputable def bm12068 : ℝ := (45342070621195093401 / 100000000000000000000)

theorem positive12068 :
    Eplus aL (agent12068.root+dsL) scalar12068.worldRadius world12068.frame
      agent12068.frame tp12068 ≤ -ep12068 := by
  apply positive_check (eT := (4647927931316118043 / 4000000000000000000)) (y := (39574581596620484711 / 100000000000000000000)) (u := (18568646016139365161 / 12500000000000000000))
  · norm_num [world12068, agent12068, scalar12068, tp12068, tm12068, ep12068, em12068, dsL]
  · norm_num [world12068, agent12068, scalar12068, tp12068, tm12068, ep12068, em12068, dsL]
  · norm_num [world12068, agent12068, scalar12068, tp12068, tm12068, ep12068, em12068, dsL]
  · norm_num [world12068, agent12068, scalar12068, tp12068, tm12068, ep12068, em12068, dsL]
  · norm_num [world12068, agent12068, scalar12068, tp12068, tm12068, ep12068, em12068, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12068, agent12068, tp12068, tm12068, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12068, agent12068, scalar12068, tp12068, tm12068, ep12068, em12068, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12068, agent12068, tp12068, tm12068, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12068, agent12068, scalar12068, tp12068, tm12068, ep12068, em12068, dsL]

theorem negative12068 :
    Eminus aL (agent12068.root+dsL) scalar12068.worldRadius world12068.frame
      agent12068.frame tm12068 ≤ -em12068 := by
  apply negative_check (lo := (16950607989647418811 / 25000000000000000000)) (hi := (13560486391717935049 / 20000000000000000000))
    (y := (-((18333780909236037597 / 25000000000000000000)))) (u := (48029670224362397167 / 100000000000000000000))
  · norm_num [world12068, agent12068, scalar12068, tp12068, tm12068, ep12068, em12068, dsL]
  · norm_num [world12068, agent12068, scalar12068, tp12068, tm12068, ep12068, em12068, dsL]
  · norm_num [world12068, agent12068, scalar12068, tp12068, tm12068, ep12068, em12068, dsL]
  · norm_num [world12068, agent12068, scalar12068, tp12068, tm12068, ep12068, em12068, dsL]
  · norm_num [world12068, agent12068, scalar12068, tp12068, tm12068, ep12068, em12068, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12068, agent12068, tp12068, tm12068, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12068, agent12068, tp12068, tm12068, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12068, agent12068, scalar12068, tp12068, tm12068, ep12068, em12068, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12068, agent12068, tp12068, tm12068, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12068, agent12068, scalar12068, tp12068, tm12068, ep12068, em12068, dsL]

theorem tails12068 :
    exp (-((12068:ℝ)*ep12068)) ≤ scalar12068.upperTail ∧
    exp (-((12068:ℝ)*em12068)) ≤ scalar12068.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12068:ℝ)) (by norm_num [ep12068]) ?_)
      (show bp12068^8 ≤ scalar12068.upperTail by norm_num [bp12068, scalar12068])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12068, bp12068, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12068:ℝ)) (by norm_num [em12068]) ?_)
      (show bm12068^8 ≤ scalar12068.lowerTail by norm_num [bm12068, scalar12068])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12068, bm12068, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12068 :
    agent12068.root+dsL+scalar12068.worldRadius < √(1/100/aL) ∧
    2*(agent12068.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12068, agent12068, scalar12068, tp12068, tm12068, ep12068, em12068, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12068, agent12068, scalar12068, tp12068, tm12068, ep12068, em12068, dsL]

noncomputable def master12068 : MasterCertificate 12068 world12068 agent12068 :=
  master scalar12068 dsL tp12068 tm12068 ep12068 em12068
    (by norm_num [dsL]) (by norm_num [tp12068]) (by norm_num [tm12068])
    (by norm_num [ep12068]) (by norm_num [em12068])
    positive12068 negative12068 tails12068.1 tails12068.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12068.1 tailGuards12068.2

theorem preserves12068 : master12068.toScalarCertificate = scalar12068 := rfl

noncomputable def tp12069 : ℝ := (1182444031 / 5000000000)
noncomputable def tm12069 : ℝ := (-((382560867 / 625000000)))
noncomputable def ep12069 : ℝ := (13590096789745721 / 25000000000000000000)
noncomputable def em12069 : ℝ := (52434500021466217 / 100000000000000000000)
noncomputable def bp12069 : ℝ := (4403900837818018701 / 10000000000000000000)
noncomputable def bm12069 : ℝ := (45337305295360953339 / 100000000000000000000)

theorem positive12069 :
    Eplus aL (agent12069.root+dsL) scalar12069.worldRadius world12069.frame
      agent12069.frame tp12069 ≤ -ep12069 := by
  apply positive_check (eT := (116198529631545094599 / 100000000000000000000)) (y := (2473452376004296929 / 6250000000000000000)) (u := (37137535809486289221 / 25000000000000000000))
  · norm_num [world12069, agent12069, scalar12069, tp12069, tm12069, ep12069, em12069, dsL]
  · norm_num [world12069, agent12069, scalar12069, tp12069, tm12069, ep12069, em12069, dsL]
  · norm_num [world12069, agent12069, scalar12069, tp12069, tm12069, ep12069, em12069, dsL]
  · norm_num [world12069, agent12069, scalar12069, tp12069, tm12069, ep12069, em12069, dsL]
  · norm_num [world12069, agent12069, scalar12069, tp12069, tm12069, ep12069, em12069, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12069, agent12069, tp12069, tm12069, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12069, agent12069, scalar12069, tp12069, tm12069, ep12069, em12069, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12069, agent12069, tp12069, tm12069, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12069, agent12069, scalar12069, tp12069, tm12069, ep12069, em12069, dsL]

theorem negative12069 :
    Eminus aL (agent12069.root+dsL) scalar12069.worldRadius world12069.frame
      agent12069.frame tm12069 ≤ -em12069 := by
  apply negative_check (lo := (16950520095843527267 / 25000000000000000000)) (hi := (67802080383374109069 / 100000000000000000000))
    (y := (-((73334749223326335787 / 100000000000000000000)))) (u := (48029850054324962349 / 100000000000000000000))
  · norm_num [world12069, agent12069, scalar12069, tp12069, tm12069, ep12069, em12069, dsL]
  · norm_num [world12069, agent12069, scalar12069, tp12069, tm12069, ep12069, em12069, dsL]
  · norm_num [world12069, agent12069, scalar12069, tp12069, tm12069, ep12069, em12069, dsL]
  · norm_num [world12069, agent12069, scalar12069, tp12069, tm12069, ep12069, em12069, dsL]
  · norm_num [world12069, agent12069, scalar12069, tp12069, tm12069, ep12069, em12069, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12069, agent12069, tp12069, tm12069, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12069, agent12069, tp12069, tm12069, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12069, agent12069, scalar12069, tp12069, tm12069, ep12069, em12069, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12069, agent12069, tp12069, tm12069, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12069, agent12069, scalar12069, tp12069, tm12069, ep12069, em12069, dsL]

theorem tails12069 :
    exp (-((12069:ℝ)*ep12069)) ≤ scalar12069.upperTail ∧
    exp (-((12069:ℝ)*em12069)) ≤ scalar12069.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12069:ℝ)) (by norm_num [ep12069]) ?_)
      (show bp12069^8 ≤ scalar12069.upperTail by norm_num [bp12069, scalar12069])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12069, bp12069, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12069:ℝ)) (by norm_num [em12069]) ?_)
      (show bm12069^8 ≤ scalar12069.lowerTail by norm_num [bm12069, scalar12069])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12069, bm12069, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12069 :
    agent12069.root+dsL+scalar12069.worldRadius < √(1/100/aL) ∧
    2*(agent12069.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12069, agent12069, scalar12069, tp12069, tm12069, ep12069, em12069, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12069, agent12069, scalar12069, tp12069, tm12069, ep12069, em12069, dsL]

noncomputable def master12069 : MasterCertificate 12069 world12069 agent12069 :=
  master scalar12069 dsL tp12069 tm12069 ep12069 em12069
    (by norm_num [dsL]) (by norm_num [tp12069]) (by norm_num [tm12069])
    (by norm_num [ep12069]) (by norm_num [em12069])
    positive12069 negative12069 tails12069.1 tails12069.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12069.1 tailGuards12069.2

theorem preserves12069 : master12069.toScalarCertificate = scalar12069 := rfl

noncomputable def tp12070 : ℝ := (2364990163 / 10000000000)
noncomputable def tm12070 : ℝ := (-((6121203417 / 10000000000)))
noncomputable def ep12070 : ℝ := (27181697970927227 / 50000000000000000000)
noncomputable def em12070 : ℝ := (26218560578121439 / 50000000000000000000)
noncomputable def bp12070 : ℝ := (44034017037831513107 / 100000000000000000000)
noncomputable def bm12070 : ℝ := (11333135267784546229 / 25000000000000000000)

theorem positive12070 :
    Eplus aL (agent12070.root+dsL) scalar12070.worldRadius world12070.frame
      agent12070.frame tp12070 ≤ -ep12070 := by
  apply positive_check (eT := (14524857566234782981 / 12500000000000000000)) (y := (39575894058324981663 / 100000000000000000000)) (u := (37137779448213307923 / 25000000000000000000))
  · norm_num [world12070, agent12070, scalar12070, tp12070, tm12070, ep12070, em12070, dsL]
  · norm_num [world12070, agent12070, scalar12070, tp12070, tm12070, ep12070, em12070, dsL]
  · norm_num [world12070, agent12070, scalar12070, tp12070, tm12070, ep12070, em12070, dsL]
  · norm_num [world12070, agent12070, scalar12070, tp12070, tm12070, ep12070, em12070, dsL]
  · norm_num [world12070, agent12070, scalar12070, tp12070, tm12070, ep12070, em12070, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12070, agent12070, tp12070, tm12070, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12070, agent12070, scalar12070, tp12070, tm12070, ep12070, em12070, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12070, agent12070, tp12070, tm12070, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12070, agent12070, scalar12070, tp12070, tm12070, ep12070, em12070, dsL]

theorem negative12070 :
    Eminus aL (agent12070.root+dsL) scalar12070.worldRadius world12070.frame
      agent12070.frame tm12070 ≤ -em12070 := by
  apply negative_check (lo := (33900865041653614079 / 50000000000000000000)) (hi := (67801730083307228159 / 100000000000000000000))
    (y := (-((73334373472016484669 / 100000000000000000000)))) (u := (9606006105490945173 / 20000000000000000000))
  · norm_num [world12070, agent12070, scalar12070, tp12070, tm12070, ep12070, em12070, dsL]
  · norm_num [world12070, agent12070, scalar12070, tp12070, tm12070, ep12070, em12070, dsL]
  · norm_num [world12070, agent12070, scalar12070, tp12070, tm12070, ep12070, em12070, dsL]
  · norm_num [world12070, agent12070, scalar12070, tp12070, tm12070, ep12070, em12070, dsL]
  · norm_num [world12070, agent12070, scalar12070, tp12070, tm12070, ep12070, em12070, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12070, agent12070, tp12070, tm12070, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12070, agent12070, tp12070, tm12070, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12070, agent12070, scalar12070, tp12070, tm12070, ep12070, em12070, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12070, agent12070, tp12070, tm12070, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12070, agent12070, scalar12070, tp12070, tm12070, ep12070, em12070, dsL]

theorem tails12070 :
    exp (-((12070:ℝ)*ep12070)) ≤ scalar12070.upperTail ∧
    exp (-((12070:ℝ)*em12070)) ≤ scalar12070.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12070:ℝ)) (by norm_num [ep12070]) ?_)
      (show bp12070^8 ≤ scalar12070.upperTail by norm_num [bp12070, scalar12070])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12070, bp12070, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12070:ℝ)) (by norm_num [em12070]) ?_)
      (show bm12070^8 ≤ scalar12070.lowerTail by norm_num [bm12070, scalar12070])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12070, bm12070, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12070 :
    agent12070.root+dsL+scalar12070.worldRadius < √(1/100/aL) ∧
    2*(agent12070.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12070, agent12070, scalar12070, tp12070, tm12070, ep12070, em12070, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12070, agent12070, scalar12070, tp12070, tm12070, ep12070, em12070, dsL]

noncomputable def master12070 : MasterCertificate 12070 world12070 agent12070 :=
  master scalar12070 dsL tp12070 tm12070 ep12070 em12070
    (by norm_num [dsL]) (by norm_num [tp12070]) (by norm_num [tm12070])
    (by norm_num [ep12070]) (by norm_num [em12070])
    positive12070 negative12070 tails12070.1 tails12070.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12070.1 tailGuards12070.2

theorem preserves12070 : master12070.toScalarCertificate = scalar12070 := rfl

noncomputable def tp12071 : ℝ := (473018451 / 2000000000)
noncomputable def tm12071 : ℝ := (-((191294779 / 312500000)))
noncomputable def ep12071 : ℝ := (54366402323996721 / 100000000000000000000)
noncomputable def em12071 : ℝ := (52439740099579571 / 100000000000000000000)
noncomputable def bp12071 : ℝ := (4402902752691992653 / 10000000000000000000)
noncomputable def bm12071 : ℝ := (45327778549345871129 / 100000000000000000000)

theorem positive12071 :
    Eplus aL (agent12071.root+dsL) scalar12071.worldRadius world12071.frame
      agent12071.frame tp12071 ≤ -ep12071 := by
  apply positive_check (eT := (23239838279684056727 / 20000000000000000000)) (y := (19788275266379474517 / 50000000000000000000)) (u := (4642252906130121601 / 3125000000000000000))
  · norm_num [world12071, agent12071, scalar12071, tp12071, tm12071, ep12071, em12071, dsL]
  · norm_num [world12071, agent12071, scalar12071, tp12071, tm12071, ep12071, em12071, dsL]
  · norm_num [world12071, agent12071, scalar12071, tp12071, tm12071, ep12071, em12071, dsL]
  · norm_num [world12071, agent12071, scalar12071, tp12071, tm12071, ep12071, em12071, dsL]
  · norm_num [world12071, agent12071, scalar12071, tp12071, tm12071, ep12071, em12071, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12071, agent12071, tp12071, tm12071, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12071, agent12071, scalar12071, tp12071, tm12071, ep12071, em12071, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12071, agent12071, tp12071, tm12071, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12071, agent12071, scalar12071, tp12071, tm12071, ep12071, em12071, dsL]

theorem negative12071 :
    Eminus aL (agent12071.root+dsL) scalar12071.worldRadius world12071.frame
      agent12071.frame tm12071 ≤ -em12071 := by
  apply negative_check (lo := (67801379870308738613 / 100000000000000000000)) (hi := (33900689935154369307 / 50000000000000000000))
    (y := (-((14666799646665997273 / 20000000000000000000)))) (u := (48030210755048543437 / 100000000000000000000))
  · norm_num [world12071, agent12071, scalar12071, tp12071, tm12071, ep12071, em12071, dsL]
  · norm_num [world12071, agent12071, scalar12071, tp12071, tm12071, ep12071, em12071, dsL]
  · norm_num [world12071, agent12071, scalar12071, tp12071, tm12071, ep12071, em12071, dsL]
  · norm_num [world12071, agent12071, scalar12071, tp12071, tm12071, ep12071, em12071, dsL]
  · norm_num [world12071, agent12071, scalar12071, tp12071, tm12071, ep12071, em12071, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12071, agent12071, tp12071, tm12071, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12071, agent12071, tp12071, tm12071, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12071, agent12071, scalar12071, tp12071, tm12071, ep12071, em12071, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12071, agent12071, tp12071, tm12071, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12071, agent12071, scalar12071, tp12071, tm12071, ep12071, em12071, dsL]

theorem tails12071 :
    exp (-((12071:ℝ)*ep12071)) ≤ scalar12071.upperTail ∧
    exp (-((12071:ℝ)*em12071)) ≤ scalar12071.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12071:ℝ)) (by norm_num [ep12071]) ?_)
      (show bp12071^8 ≤ scalar12071.upperTail by norm_num [bp12071, scalar12071])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12071, bp12071, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12071:ℝ)) (by norm_num [em12071]) ?_)
      (show bm12071^8 ≤ scalar12071.lowerTail by norm_num [bm12071, scalar12071])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12071, bm12071, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12071 :
    agent12071.root+dsL+scalar12071.worldRadius < √(1/100/aL) ∧
    2*(agent12071.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12071, agent12071, scalar12071, tp12071, tm12071, ep12071, em12071, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12071, agent12071, scalar12071, tp12071, tm12071, ep12071, em12071, dsL]

noncomputable def master12071 : MasterCertificate 12071 world12071 agent12071 :=
  master scalar12071 dsL tp12071 tm12071 ep12071 em12071
    (by norm_num [dsL]) (by norm_num [tp12071]) (by norm_num [tm12071])
    (by norm_num [ep12071]) (by norm_num [em12071])
    positive12071 negative12071 tails12071.1 tails12071.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12071.1 tailGuards12071.2

theorem preserves12071 : master12071.toScalarCertificate = scalar12071 := rfl

noncomputable def tp12072 : ℝ := (94607771 / 400000000)
noncomputable def tm12072 : ℝ := (-((612166241 / 1000000000)))
noncomputable def ep12072 : ℝ := (54369408012977459 / 100000000000000000000)
noncomputable def em12072 : ℝ := (13110589591519881 / 25000000000000000000)
noncomputable def bp12072 : ℝ := (44024038710971943649 / 100000000000000000000)
noncomputable def bm12072 : ℝ := (2832688543378193427 / 6250000000000000000)

theorem positive12072 :
    Eplus aL (agent12072.root+dsL) scalar12072.worldRadius world12072.frame
      agent12072.frame tp12072 ≤ -ep12072 := by
  apply positive_check (eT := (11619952177243265807 / 10000000000000000000)) (y := (19788603101287205819 / 50000000000000000000)) (u := (5942122680423642433 / 4000000000000000000))
  · norm_num [world12072, agent12072, scalar12072, tp12072, tm12072, ep12072, em12072, dsL]
  · norm_num [world12072, agent12072, scalar12072, tp12072, tm12072, ep12072, em12072, dsL]
  · norm_num [world12072, agent12072, scalar12072, tp12072, tm12072, ep12072, em12072, dsL]
  · norm_num [world12072, agent12072, scalar12072, tp12072, tm12072, ep12072, em12072, dsL]
  · norm_num [world12072, agent12072, scalar12072, tp12072, tm12072, ep12072, em12072, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12072, agent12072, tp12072, tm12072, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12072, agent12072, scalar12072, tp12072, tm12072, ep12072, em12072, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12072, agent12072, tp12072, tm12072, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12072, agent12072, scalar12072, tp12072, tm12072, ep12072, em12072, dsL]

theorem negative12072 :
    Eminus aL (agent12072.root+dsL) scalar12072.worldRadius world12072.frame
      agent12072.frame tm12072 ≤ -em12072 := by
  apply negative_check (lo := (8475128715364746451 / 12500000000000000000)) (hi := (67801029722917971609 / 100000000000000000000))
    (y := (-((73333623821531365619 / 100000000000000000000)))) (u := (4803039058616116699 / 10000000000000000000))
  · norm_num [world12072, agent12072, scalar12072, tp12072, tm12072, ep12072, em12072, dsL]
  · norm_num [world12072, agent12072, scalar12072, tp12072, tm12072, ep12072, em12072, dsL]
  · norm_num [world12072, agent12072, scalar12072, tp12072, tm12072, ep12072, em12072, dsL]
  · norm_num [world12072, agent12072, scalar12072, tp12072, tm12072, ep12072, em12072, dsL]
  · norm_num [world12072, agent12072, scalar12072, tp12072, tm12072, ep12072, em12072, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12072, agent12072, tp12072, tm12072, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12072, agent12072, tp12072, tm12072, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12072, agent12072, scalar12072, tp12072, tm12072, ep12072, em12072, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12072, agent12072, tp12072, tm12072, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12072, agent12072, scalar12072, tp12072, tm12072, ep12072, em12072, dsL]

theorem tails12072 :
    exp (-((12072:ℝ)*ep12072)) ≤ scalar12072.upperTail ∧
    exp (-((12072:ℝ)*em12072)) ≤ scalar12072.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12072:ℝ)) (by norm_num [ep12072]) ?_)
      (show bp12072^8 ≤ scalar12072.upperTail by norm_num [bp12072, scalar12072])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12072, bp12072, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12072:ℝ)) (by norm_num [em12072]) ?_)
      (show bm12072^8 ≤ scalar12072.lowerTail by norm_num [bm12072, scalar12072])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12072, bm12072, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12072 :
    agent12072.root+dsL+scalar12072.worldRadius < √(1/100/aL) ∧
    2*(agent12072.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12072, agent12072, scalar12072, tp12072, tm12072, ep12072, em12072, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12072, agent12072, scalar12072, tp12072, tm12072, ep12072, em12072, dsL]

noncomputable def master12072 : MasterCertificate 12072 world12072 agent12072 :=
  master scalar12072 dsL tp12072 tm12072 ep12072 em12072
    (by norm_num [dsL]) (by norm_num [tp12072]) (by norm_num [tm12072])
    (by norm_num [ep12072]) (by norm_num [em12072])
    positive12072 negative12072 tails12072.1 tails12072.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12072.1 tailGuards12072.2

theorem preserves12072 : master12072.toScalarCertificate = scalar12072 := rfl

noncomputable def tp12073 : ℝ := (2365296191 / 10000000000)
noncomputable def tm12073 : ℝ := (-((6121891601 / 10000000000)))
noncomputable def ep12073 : ℝ := (54372411843101243 / 100000000000000000000)
noncomputable def em12073 : ℝ := (26222487438483013 / 50000000000000000000)
noncomputable def bp12073 : ℝ := (22009525682184129359 / 50000000000000000000)
noncomputable def bm12073 : ℝ := (45318256243049189549 / 100000000000000000000)

theorem positive12073 :
    Eplus aL (agent12073.root+dsL) scalar12073.worldRadius world12073.frame
      agent12073.frame tp12073 ≤ -ep12073 := by
  apply positive_check (eT := (23239970283179961999 / 20000000000000000000)) (y := (9894465215264842959 / 25000000000000000000)) (u := (148554039529032248041 / 100000000000000000000))
  · norm_num [world12073, agent12073, scalar12073, tp12073, tm12073, ep12073, em12073, dsL]
  · norm_num [world12073, agent12073, scalar12073, tp12073, tm12073, ep12073, em12073, dsL]
  · norm_num [world12073, agent12073, scalar12073, tp12073, tm12073, ep12073, em12073, dsL]
  · norm_num [world12073, agent12073, scalar12073, tp12073, tm12073, ep12073, em12073, dsL]
  · norm_num [world12073, agent12073, scalar12073, tp12073, tm12073, ep12073, em12073, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12073, agent12073, tp12073, tm12073, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12073, agent12073, scalar12073, tp12073, tm12073, ep12073, em12073, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12073, agent12073, tp12073, tm12073, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12073, agent12073, scalar12073, tp12073, tm12073, ep12073, em12073, dsL]

theorem negative12073 :
    Eminus aL (agent12073.root+dsL) scalar12073.worldRadius world12073.frame
      agent12073.frame tm12073 ≤ -em12073 := by
  apply negative_check (lo := (2712027230749661273 / 4000000000000000000)) (hi := (33900340384370765913 / 50000000000000000000))
    (y := (-((73333248127133350939 / 100000000000000000000)))) (u := (24015285516993454871 / 50000000000000000000))
  · norm_num [world12073, agent12073, scalar12073, tp12073, tm12073, ep12073, em12073, dsL]
  · norm_num [world12073, agent12073, scalar12073, tp12073, tm12073, ep12073, em12073, dsL]
  · norm_num [world12073, agent12073, scalar12073, tp12073, tm12073, ep12073, em12073, dsL]
  · norm_num [world12073, agent12073, scalar12073, tp12073, tm12073, ep12073, em12073, dsL]
  · norm_num [world12073, agent12073, scalar12073, tp12073, tm12073, ep12073, em12073, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12073, agent12073, tp12073, tm12073, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12073, agent12073, tp12073, tm12073, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12073, agent12073, scalar12073, tp12073, tm12073, ep12073, em12073, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12073, agent12073, tp12073, tm12073, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12073, agent12073, scalar12073, tp12073, tm12073, ep12073, em12073, dsL]

theorem tails12073 :
    exp (-((12073:ℝ)*ep12073)) ≤ scalar12073.upperTail ∧
    exp (-((12073:ℝ)*em12073)) ≤ scalar12073.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12073:ℝ)) (by norm_num [ep12073]) ?_)
      (show bp12073^8 ≤ scalar12073.upperTail by norm_num [bp12073, scalar12073])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12073, bp12073, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12073:ℝ)) (by norm_num [em12073]) ?_)
      (show bm12073^8 ≤ scalar12073.lowerTail by norm_num [bm12073, scalar12073])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12073, bm12073, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12073 :
    agent12073.root+dsL+scalar12073.worldRadius < √(1/100/aL) ∧
    2*(agent12073.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12073, agent12073, scalar12073, tp12073, tm12073, ep12073, em12073, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12073, agent12073, scalar12073, tp12073, tm12073, ep12073, em12073, dsL]

noncomputable def master12073 : MasterCertificate 12073 world12073 agent12073 :=
  master scalar12073 dsL tp12073 tm12073 ep12073 em12073
    (by norm_num [dsL]) (by norm_num [tp12073]) (by norm_num [tm12073])
    (by norm_num [ep12073]) (by norm_num [em12073])
    positive12073 negative12073 tails12073.1 tails12073.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12073.1 tailGuards12073.2

theorem preserves12073 : master12073.toScalarCertificate = scalar12073 := rfl

noncomputable def tp12074 : ℝ := (2365398129 / 10000000000)
noncomputable def tm12074 : ℝ := (-((6122120671 / 10000000000)))
noncomputable def ep12074 : ℝ := (54375413493147111 / 100000000000000000000)
noncomputable def em12074 : ℝ := (1311189733848669 / 2500000000000000000)
noncomputable def bp12074 : ℝ := (8802813140085153437 / 20000000000000000000)
noncomputable def bm12074 : ℝ := (45313497386623494823 / 100000000000000000000)

theorem positive12074 :
    Eplus aL (agent12074.root+dsL) scalar12074.worldRadius world12074.frame
      agent12074.frame tp12074 ≤ -ep12074 := by
  apply positive_check (eT := (58100090629131575257 / 50000000000000000000)) (y := (39578516670217030189 / 100000000000000000000)) (u := (14855501376322210587 / 10000000000000000000))
  · norm_num [world12074, agent12074, scalar12074, tp12074, tm12074, ep12074, em12074, dsL]
  · norm_num [world12074, agent12074, scalar12074, tp12074, tm12074, ep12074, em12074, dsL]
  · norm_num [world12074, agent12074, scalar12074, tp12074, tm12074, ep12074, em12074, dsL]
  · norm_num [world12074, agent12074, scalar12074, tp12074, tm12074, ep12074, em12074, dsL]
  · norm_num [world12074, agent12074, scalar12074, tp12074, tm12074, ep12074, em12074, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12074, agent12074, tp12074, tm12074, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12074, agent12074, scalar12074, tp12074, tm12074, ep12074, em12074, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12074, agent12074, tp12074, tm12074, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12074, agent12074, scalar12074, tp12074, tm12074, ep12074, em12074, dsL]

theorem negative12074 :
    Eminus aL (agent12074.root+dsL) scalar12074.worldRadius world12074.frame
      agent12074.frame tm12074 ≤ -em12074 := by
  apply negative_check (lo := (67800332275997158041 / 100000000000000000000)) (hi := (33900166137998579021 / 50000000000000000000))
    (y := (-((36666436195151183573 / 50000000000000000000)))) (u := (24015375751435730043 / 50000000000000000000))
  · norm_num [world12074, agent12074, scalar12074, tp12074, tm12074, ep12074, em12074, dsL]
  · norm_num [world12074, agent12074, scalar12074, tp12074, tm12074, ep12074, em12074, dsL]
  · norm_num [world12074, agent12074, scalar12074, tp12074, tm12074, ep12074, em12074, dsL]
  · norm_num [world12074, agent12074, scalar12074, tp12074, tm12074, ep12074, em12074, dsL]
  · norm_num [world12074, agent12074, scalar12074, tp12074, tm12074, ep12074, em12074, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12074, agent12074, tp12074, tm12074, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12074, agent12074, tp12074, tm12074, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12074, agent12074, scalar12074, tp12074, tm12074, ep12074, em12074, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12074, agent12074, tp12074, tm12074, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12074, agent12074, scalar12074, tp12074, tm12074, ep12074, em12074, dsL]

theorem tails12074 :
    exp (-((12074:ℝ)*ep12074)) ≤ scalar12074.upperTail ∧
    exp (-((12074:ℝ)*em12074)) ≤ scalar12074.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12074:ℝ)) (by norm_num [ep12074]) ?_)
      (show bp12074^8 ≤ scalar12074.upperTail by norm_num [bp12074, scalar12074])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12074, bp12074, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12074:ℝ)) (by norm_num [em12074]) ?_)
      (show bm12074^8 ≤ scalar12074.lowerTail by norm_num [bm12074, scalar12074])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12074, bm12074, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12074 :
    agent12074.root+dsL+scalar12074.worldRadius < √(1/100/aL) ∧
    2*(agent12074.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12074, agent12074, scalar12074, tp12074, tm12074, ep12074, em12074, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12074, agent12074, scalar12074, tp12074, tm12074, ep12074, em12074, dsL]

noncomputable def master12074 : MasterCertificate 12074 world12074 agent12074 :=
  master scalar12074 dsL tp12074 tm12074 ep12074 em12074
    (by norm_num [dsL]) (by norm_num [tp12074]) (by norm_num [tm12074])
    (by norm_num [ep12074]) (by norm_num [em12074])
    positive12074 negative12074 tails12074.1 tails12074.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12074.1 tailGuards12074.2

theorem preserves12074 : master12074.toScalarCertificate = scalar12074 := rfl

noncomputable def tp12075 : ℝ := (36960937 / 156250000)
noncomputable def tm12075 : ℝ := (-((1224469933 / 2000000000)))
noncomputable def ep12075 : ℝ := (27189206798536809 / 50000000000000000000)
noncomputable def em12075 : ℝ := (13112550599445171 / 25000000000000000000)
noncomputable def bp12075 : ℝ := (44009081297945860733 / 100000000000000000000)
noncomputable def bm12075 : ℝ := (4530873971387593739 / 10000000000000000000)

theorem positive12075 :
    Eplus aL (agent12075.root+dsL) scalar12075.worldRadius world12075.frame
      agent12075.frame tp12075 ≤ -ep12075 := by
  apply positive_check (eT := (2324010208139650293 / 2000000000000000000)) (y := (19789585618811336661 / 50000000000000000000)) (u := (148555986159104138369 / 100000000000000000000))
  · norm_num [world12075, agent12075, scalar12075, tp12075, tm12075, ep12075, em12075, dsL]
  · norm_num [world12075, agent12075, scalar12075, tp12075, tm12075, ep12075, em12075, dsL]
  · norm_num [world12075, agent12075, scalar12075, tp12075, tm12075, ep12075, em12075, dsL]
  · norm_num [world12075, agent12075, scalar12075, tp12075, tm12075, ep12075, em12075, dsL]
  · norm_num [world12075, agent12075, scalar12075, tp12075, tm12075, ep12075, em12075, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12075, agent12075, tp12075, tm12075, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12075, agent12075, scalar12075, tp12075, tm12075, ep12075, em12075, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12075, agent12075, tp12075, tm12075, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12075, agent12075, scalar12075, tp12075, tm12075, ep12075, em12075, dsL]

theorem negative12075 :
    Eminus aL (agent12075.root+dsL) scalar12075.worldRadius world12075.frame
      agent12075.frame tm12075 ≤ -em12075 := by
  apply negative_check (lo := (67799984051094040531 / 100000000000000000000)) (hi := (16949996012773510133 / 25000000000000000000))
    (y := (-((14666499376877071583 / 20000000000000000000)))) (u := (24015465930761982931 / 50000000000000000000))
  · norm_num [world12075, agent12075, scalar12075, tp12075, tm12075, ep12075, em12075, dsL]
  · norm_num [world12075, agent12075, scalar12075, tp12075, tm12075, ep12075, em12075, dsL]
  · norm_num [world12075, agent12075, scalar12075, tp12075, tm12075, ep12075, em12075, dsL]
  · norm_num [world12075, agent12075, scalar12075, tp12075, tm12075, ep12075, em12075, dsL]
  · norm_num [world12075, agent12075, scalar12075, tp12075, tm12075, ep12075, em12075, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12075, agent12075, tp12075, tm12075, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12075, agent12075, tp12075, tm12075, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12075, agent12075, scalar12075, tp12075, tm12075, ep12075, em12075, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12075, agent12075, tp12075, tm12075, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12075, agent12075, scalar12075, tp12075, tm12075, ep12075, em12075, dsL]

theorem tails12075 :
    exp (-((12075:ℝ)*ep12075)) ≤ scalar12075.upperTail ∧
    exp (-((12075:ℝ)*em12075)) ≤ scalar12075.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12075:ℝ)) (by norm_num [ep12075]) ?_)
      (show bp12075^8 ≤ scalar12075.upperTail by norm_num [bp12075, scalar12075])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12075, bp12075, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12075:ℝ)) (by norm_num [em12075]) ?_)
      (show bm12075^8 ≤ scalar12075.lowerTail by norm_num [bm12075, scalar12075])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12075, bm12075, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12075 :
    agent12075.root+dsL+scalar12075.worldRadius < √(1/100/aL) ∧
    2*(agent12075.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12075, agent12075, scalar12075, tp12075, tm12075, ep12075, em12075, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12075, agent12075, scalar12075, tp12075, tm12075, ep12075, em12075, dsL]

noncomputable def master12075 : MasterCertificate 12075 world12075 agent12075 :=
  master scalar12075 dsL tp12075 tm12075 ep12075 em12075
    (by norm_num [dsL]) (by norm_num [tp12075]) (by norm_num [tm12075])
    (by norm_num [ep12075]) (by norm_num [em12075])
    positive12075 negative12075 tails12075.1 tails12075.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12075.1 tailGuards12075.2

theorem preserves12075 : master12075.toScalarCertificate = scalar12075 := rfl

noncomputable def tp12076 : ℝ := (295700217 / 1250000000)
noncomputable def tm12076 : ℝ := (-((1224515699 / 2000000000)))
noncomputable def ep12076 : ℝ := (54381412114674721 / 100000000000000000000)
noncomputable def em12076 : ℝ := (52452813981709963 / 100000000000000000000)
noncomputable def bp12076 : ℝ := (44004098183589531197 / 100000000000000000000)
noncomputable def bm12076 : ℝ := (45303983243080794649 / 100000000000000000000)

theorem positive12076 :
    Eplus aL (agent12076.root+dsL) scalar12076.worldRadius world12076.frame
      agent12076.frame tp12076 ≤ -ep12076 := by
  apply positive_check (eT := (116200839068656321831 / 100000000000000000000)) (y := (7915965034876553901 / 20000000000000000000)) (u := (148556957624483337299 / 100000000000000000000))
  · norm_num [world12076, agent12076, scalar12076, tp12076, tm12076, ep12076, em12076, dsL]
  · norm_num [world12076, agent12076, scalar12076, tp12076, tm12076, ep12076, em12076, dsL]
  · norm_num [world12076, agent12076, scalar12076, tp12076, tm12076, ep12076, em12076, dsL]
  · norm_num [world12076, agent12076, scalar12076, tp12076, tm12076, ep12076, em12076, dsL]
  · norm_num [world12076, agent12076, scalar12076, tp12076, tm12076, ep12076, em12076, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12076, agent12076, tp12076, tm12076, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12076, agent12076, scalar12076, tp12076, tm12076, ep12076, em12076, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12076, agent12076, tp12076, tm12076, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12076, agent12076, scalar12076, tp12076, tm12076, ep12076, em12076, dsL]

theorem negative12076 :
    Eminus aL (agent12076.root+dsL) scalar12076.worldRadius world12076.frame
      agent12076.frame tm12076 ≤ -em12076 := by
  apply negative_check (lo := (13559927294529792367 / 20000000000000000000)) (hi := (16949909118162240459 / 25000000000000000000))
    (y := (-((73332121167589558579 / 100000000000000000000)))) (u := (9606222464428231751 / 20000000000000000000))
  · norm_num [world12076, agent12076, scalar12076, tp12076, tm12076, ep12076, em12076, dsL]
  · norm_num [world12076, agent12076, scalar12076, tp12076, tm12076, ep12076, em12076, dsL]
  · norm_num [world12076, agent12076, scalar12076, tp12076, tm12076, ep12076, em12076, dsL]
  · norm_num [world12076, agent12076, scalar12076, tp12076, tm12076, ep12076, em12076, dsL]
  · norm_num [world12076, agent12076, scalar12076, tp12076, tm12076, ep12076, em12076, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12076, agent12076, tp12076, tm12076, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12076, agent12076, tp12076, tm12076, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12076, agent12076, scalar12076, tp12076, tm12076, ep12076, em12076, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12076, agent12076, tp12076, tm12076, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12076, agent12076, scalar12076, tp12076, tm12076, ep12076, em12076, dsL]

theorem tails12076 :
    exp (-((12076:ℝ)*ep12076)) ≤ scalar12076.upperTail ∧
    exp (-((12076:ℝ)*em12076)) ≤ scalar12076.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12076:ℝ)) (by norm_num [ep12076]) ?_)
      (show bp12076^8 ≤ scalar12076.upperTail by norm_num [bp12076, scalar12076])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12076, bp12076, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12076:ℝ)) (by norm_num [em12076]) ?_)
      (show bm12076^8 ≤ scalar12076.lowerTail by norm_num [bm12076, scalar12076])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12076, bm12076, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12076 :
    agent12076.root+dsL+scalar12076.worldRadius < √(1/100/aL) ∧
    2*(agent12076.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12076, agent12076, scalar12076, tp12076, tm12076, ep12076, em12076, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12076, agent12076, scalar12076, tp12076, tm12076, ep12076, em12076, dsL]

noncomputable def master12076 : MasterCertificate 12076 world12076 agent12076 :=
  master scalar12076 dsL tp12076 tm12076 ep12076 em12076
    (by norm_num [dsL]) (by norm_num [tp12076]) (by norm_num [tm12076])
    (by norm_num [ep12076]) (by norm_num [em12076])
    positive12076 negative12076 tails12076.1 tails12076.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12076.1 tailGuards12076.2

theorem preserves12076 : master12076.toScalarCertificate = scalar12076 := rfl

noncomputable def tp12077 : ℝ := (2365703461 / 10000000000)
noncomputable def tm12077 : ℝ := (-((6122807219 / 10000000000)))
noncomputable def ep12077 : ℝ := (13596102326665779 / 25000000000000000000)
noncomputable def em12077 : ℝ := (26227712144909007 / 50000000000000000000)
noncomputable def bp12077 : ℝ := (43999116184137755747 / 100000000000000000000)
noncomputable def bm12077 : ℝ := (22649613924163616871 / 50000000000000000000)

theorem positive12077 :
    Eplus aL (agent12077.root+dsL) scalar12077.worldRadius world12077.frame
      agent12077.frame tp12077 ≤ -ep12077 := by
  apply positive_check (eT := (5810058372489144033 / 5000000000000000000)) (y := (7916095807777400367 / 20000000000000000000)) (u := (37139482247218377819 / 25000000000000000000))
  · norm_num [world12077, agent12077, scalar12077, tp12077, tm12077, ep12077, em12077, dsL]
  · norm_num [world12077, agent12077, scalar12077, tp12077, tm12077, ep12077, em12077, dsL]
  · norm_num [world12077, agent12077, scalar12077, tp12077, tm12077, ep12077, em12077, dsL]
  · norm_num [world12077, agent12077, scalar12077, tp12077, tm12077, ep12077, em12077, dsL]
  · norm_num [world12077, agent12077, scalar12077, tp12077, tm12077, ep12077, em12077, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12077, agent12077, tp12077, tm12077, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12077, agent12077, scalar12077, tp12077, tm12077, ep12077, em12077, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12077, agent12077, tp12077, tm12077, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12077, agent12077, scalar12077, tp12077, tm12077, ep12077, em12077, dsL]

theorem negative12077 :
    Eminus aL (agent12077.root+dsL) scalar12077.worldRadius world12077.frame
      agent12077.frame tm12077 ≤ -em12077 := by
  apply negative_check (lo := (33899644645541154093 / 50000000000000000000)) (hi := (67799289291082308187 / 100000000000000000000))
    (y := (-((733317456862927747 / 1000000000000000000)))) (u := (24015646335161576143 / 50000000000000000000))
  · norm_num [world12077, agent12077, scalar12077, tp12077, tm12077, ep12077, em12077, dsL]
  · norm_num [world12077, agent12077, scalar12077, tp12077, tm12077, ep12077, em12077, dsL]
  · norm_num [world12077, agent12077, scalar12077, tp12077, tm12077, ep12077, em12077, dsL]
  · norm_num [world12077, agent12077, scalar12077, tp12077, tm12077, ep12077, em12077, dsL]
  · norm_num [world12077, agent12077, scalar12077, tp12077, tm12077, ep12077, em12077, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12077, agent12077, tp12077, tm12077, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12077, agent12077, tp12077, tm12077, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12077, agent12077, scalar12077, tp12077, tm12077, ep12077, em12077, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12077, agent12077, tp12077, tm12077, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12077, agent12077, scalar12077, tp12077, tm12077, ep12077, em12077, dsL]

theorem tails12077 :
    exp (-((12077:ℝ)*ep12077)) ≤ scalar12077.upperTail ∧
    exp (-((12077:ℝ)*em12077)) ≤ scalar12077.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12077:ℝ)) (by norm_num [ep12077]) ?_)
      (show bp12077^8 ≤ scalar12077.upperTail by norm_num [bp12077, scalar12077])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12077, bp12077, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12077:ℝ)) (by norm_num [em12077]) ?_)
      (show bm12077^8 ≤ scalar12077.lowerTail by norm_num [bm12077, scalar12077])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12077, bm12077, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12077 :
    agent12077.root+dsL+scalar12077.worldRadius < √(1/100/aL) ∧
    2*(agent12077.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12077, agent12077, scalar12077, tp12077, tm12077, ep12077, em12077, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12077, agent12077, scalar12077, tp12077, tm12077, ep12077, em12077, dsL]

noncomputable def master12077 : MasterCertificate 12077 world12077 agent12077 :=
  master scalar12077 dsL tp12077 tm12077 ep12077 em12077
    (by norm_num [dsL]) (by norm_num [tp12077]) (by norm_num [tm12077])
    (by norm_num [ep12077]) (by norm_num [em12077])
    positive12077 negative12077 tails12077.1 tails12077.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12077.1 tailGuards12077.2

theorem preserves12077 : master12077.toScalarCertificate = scalar12077 := rfl

noncomputable def tp12078 : ℝ := (2365805227 / 10000000000)
noncomputable def tm12078 : ℝ := (-((1530758921 / 2500000000)))
noncomputable def ep12078 : ℝ := (13596851079844707 / 25000000000000000000)
noncomputable def em12078 : ℝ := (13114508141256049 / 25000000000000000000)
noncomputable def bp12078 : ℝ := (5499266983320063959 / 12500000000000000000)
noncomputable def bm12078 : ℝ := (45294474047314899931 / 100000000000000000000)

theorem positive12078 :
    Eplus aL (agent12078.root+dsL) scalar12078.worldRadius world12078.frame
      agent12078.frame tp12078 ≤ -ep12078 := by
  apply positive_check (eT := (11620149616993677757 / 10000000000000000000)) (y := (39581134394749260381 / 100000000000000000000)) (u := (4642465705473756677 / 3125000000000000000))
  · norm_num [world12078, agent12078, scalar12078, tp12078, tm12078, ep12078, em12078, dsL]
  · norm_num [world12078, agent12078, scalar12078, tp12078, tm12078, ep12078, em12078, dsL]
  · norm_num [world12078, agent12078, scalar12078, tp12078, tm12078, ep12078, em12078, dsL]
  · norm_num [world12078, agent12078, scalar12078, tp12078, tm12078, ep12078, em12078, dsL]
  · norm_num [world12078, agent12078, scalar12078, tp12078, tm12078, ep12078, em12078, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12078, agent12078, tp12078, tm12078, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12078, agent12078, scalar12078, tp12078, tm12078, ep12078, em12078, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12078, agent12078, tp12078, tm12078, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12078, agent12078, scalar12078, tp12078, tm12078, ep12078, em12078, dsL]

theorem negative12078 :
    Eminus aL (agent12078.root+dsL) scalar12078.worldRadius world12078.frame
      agent12078.frame tm12078 ≤ -em12078 := by
  apply negative_check (lo := (8474867895585167467 / 12500000000000000000)) (hi := (67798943164681339737 / 100000000000000000000))
    (y := (-((7333136880724683929 / 10000000000000000000)))) (u := (48031473690541832067 / 100000000000000000000))
  · norm_num [world12078, agent12078, scalar12078, tp12078, tm12078, ep12078, em12078, dsL]
  · norm_num [world12078, agent12078, scalar12078, tp12078, tm12078, ep12078, em12078, dsL]
  · norm_num [world12078, agent12078, scalar12078, tp12078, tm12078, ep12078, em12078, dsL]
  · norm_num [world12078, agent12078, scalar12078, tp12078, tm12078, ep12078, em12078, dsL]
  · norm_num [world12078, agent12078, scalar12078, tp12078, tm12078, ep12078, em12078, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12078, agent12078, tp12078, tm12078, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12078, agent12078, tp12078, tm12078, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12078, agent12078, scalar12078, tp12078, tm12078, ep12078, em12078, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12078, agent12078, tp12078, tm12078, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12078, agent12078, scalar12078, tp12078, tm12078, ep12078, em12078, dsL]

theorem tails12078 :
    exp (-((12078:ℝ)*ep12078)) ≤ scalar12078.upperTail ∧
    exp (-((12078:ℝ)*em12078)) ≤ scalar12078.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12078:ℝ)) (by norm_num [ep12078]) ?_)
      (show bp12078^8 ≤ scalar12078.upperTail by norm_num [bp12078, scalar12078])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12078, bp12078, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12078:ℝ)) (by norm_num [em12078]) ?_)
      (show bm12078^8 ≤ scalar12078.lowerTail by norm_num [bm12078, scalar12078])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12078, bm12078, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12078 :
    agent12078.root+dsL+scalar12078.worldRadius < √(1/100/aL) ∧
    2*(agent12078.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12078, agent12078, scalar12078, tp12078, tm12078, ep12078, em12078, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12078, agent12078, scalar12078, tp12078, tm12078, ep12078, em12078, dsL]

noncomputable def master12078 : MasterCertificate 12078 world12078 agent12078 :=
  master scalar12078 dsL tp12078 tm12078 ep12078 em12078
    (by norm_num [dsL]) (by norm_num [tp12078]) (by norm_num [tm12078])
    (by norm_num [ep12078]) (by norm_num [em12078])
    positive12078 negative12078 tails12078.1 tails12078.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12078.1 tailGuards12078.2

theorem preserves12078 : master12078.toScalarCertificate = scalar12078 := rfl

noncomputable def tp12079 : ℝ := (1182953403 / 5000000000)
noncomputable def tm12079 : ℝ := (-((1224652843 / 2000000000)))
noncomputable def ep12079 : ℝ := (54390398122708143 / 100000000000000000000)
noncomputable def em12079 : ℝ := (26230319849469177 / 50000000000000000000)
noncomputable def bp12079 : ℝ := (43989156586593527729 / 100000000000000000000)
noncomputable def bm12079 : ℝ := (4528972123029303083 / 10000000000000000000)

theorem positive12079 :
    Eplus aL (agent12079.root+dsL) scalar12079.worldRadius world12079.frame
      agent12079.frame tp12079 ≤ -ep12079 := by
  apply positive_check (eT := (7262613971721405951 / 6250000000000000000)) (y := (7916357405996566991 / 20000000000000000000)) (u := (148559872126064842849 / 100000000000000000000))
  · norm_num [world12079, agent12079, scalar12079, tp12079, tm12079, ep12079, em12079, dsL]
  · norm_num [world12079, agent12079, scalar12079, tp12079, tm12079, ep12079, em12079, dsL]
  · norm_num [world12079, agent12079, scalar12079, tp12079, tm12079, ep12079, em12079, dsL]
  · norm_num [world12079, agent12079, scalar12079, tp12079, tm12079, ep12079, em12079, dsL]
  · norm_num [world12079, agent12079, scalar12079, tp12079, tm12079, ep12079, em12079, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12079, agent12079, tp12079, tm12079, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12079, agent12079, scalar12079, tp12079, tm12079, ep12079, em12079, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12079, agent12079, tp12079, tm12079, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12079, agent12079, scalar12079, tp12079, tm12079, ep12079, em12079, dsL]

theorem negative12079 :
    Eminus aL (agent12079.root+dsL) scalar12079.worldRadius world12079.frame
      agent12079.frame tm12079 ≤ -em12079 := by
  apply negative_check (lo := (67798596694941005347 / 100000000000000000000)) (hi := (16949649173735251337 / 25000000000000000000))
    (y := (-((73330993973020431041 / 100000000000000000000)))) (u := (4803165372928209569 / 10000000000000000000))
  · norm_num [world12079, agent12079, scalar12079, tp12079, tm12079, ep12079, em12079, dsL]
  · norm_num [world12079, agent12079, scalar12079, tp12079, tm12079, ep12079, em12079, dsL]
  · norm_num [world12079, agent12079, scalar12079, tp12079, tm12079, ep12079, em12079, dsL]
  · norm_num [world12079, agent12079, scalar12079, tp12079, tm12079, ep12079, em12079, dsL]
  · norm_num [world12079, agent12079, scalar12079, tp12079, tm12079, ep12079, em12079, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12079, agent12079, tp12079, tm12079, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12079, agent12079, tp12079, tm12079, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12079, agent12079, scalar12079, tp12079, tm12079, ep12079, em12079, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12079, agent12079, tp12079, tm12079, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12079, agent12079, scalar12079, tp12079, tm12079, ep12079, em12079, dsL]

theorem tails12079 :
    exp (-((12079:ℝ)*ep12079)) ≤ scalar12079.upperTail ∧
    exp (-((12079:ℝ)*em12079)) ≤ scalar12079.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12079:ℝ)) (by norm_num [ep12079]) ?_)
      (show bp12079^8 ≤ scalar12079.upperTail by norm_num [bp12079, scalar12079])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12079, bp12079, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12079:ℝ)) (by norm_num [em12079]) ?_)
      (show bm12079^8 ≤ scalar12079.lowerTail by norm_num [bm12079, scalar12079])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12079, bm12079, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12079 :
    agent12079.root+dsL+scalar12079.worldRadius < √(1/100/aL) ∧
    2*(agent12079.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12079, agent12079, scalar12079, tp12079, tm12079, ep12079, em12079, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12079, agent12079, scalar12079, tp12079, tm12079, ep12079, em12079, dsL]

noncomputable def master12079 : MasterCertificate 12079 world12079 agent12079 :=
  master scalar12079 dsL tp12079 tm12079 ep12079 em12079
    (by norm_num [dsL]) (by norm_num [tp12079]) (by norm_num [tm12079])
    (by norm_num [ep12079]) (by norm_num [em12079])
    positive12079 negative12079 tails12079.1 tails12079.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12079.1 tailGuards12079.2

theorem preserves12079 : master12079.toScalarCertificate = scalar12079 := rfl

noncomputable def tp12080 : ℝ := (2366008407 / 10000000000)
noncomputable def tm12080 : ℝ := (-((6123492597 / 10000000000)))
noncomputable def ep12080 : ℝ := (2719669494931959 / 5000000000000000000)
noncomputable def em12080 : ℝ := (13115811239367457 / 25000000000000000000)
noncomputable def bp12080 : ℝ := (1374505590234476173 / 3125000000000000000)
noncomputable def bm12080 : ℝ := (1811398795968952017 / 4000000000000000000)

theorem positive12080 :
    Eplus aL (agent12080.root+dsL) scalar12080.worldRadius world12080.frame
      agent12080.frame tp12080 ≤ -ep12080 := by
  apply positive_check (eT := (29050537781005601519 / 25000000000000000000)) (y := (1236951270423025357 / 3125000000000000000)) (u := (37140210787888559583 / 25000000000000000000))
  · norm_num [world12080, agent12080, scalar12080, tp12080, tm12080, ep12080, em12080, dsL]
  · norm_num [world12080, agent12080, scalar12080, tp12080, tm12080, ep12080, em12080, dsL]
  · norm_num [world12080, agent12080, scalar12080, tp12080, tm12080, ep12080, em12080, dsL]
  · norm_num [world12080, agent12080, scalar12080, tp12080, tm12080, ep12080, em12080, dsL]
  · norm_num [world12080, agent12080, scalar12080, tp12080, tm12080, ep12080, em12080, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12080, agent12080, tp12080, tm12080, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12080, agent12080, scalar12080, tp12080, tm12080, ep12080, em12080, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12080, agent12080, tp12080, tm12080, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12080, agent12080, scalar12080, tp12080, tm12080, ep12080, em12080, dsL]

theorem negative12080 :
    Eminus aL (agent12080.root+dsL) scalar12080.worldRadius world12080.frame
      agent12080.frame tm12080 ≤ -em12080 := by
  apply negative_check (lo := (67798250807037040333 / 100000000000000000000)) (hi := (33899125403518520167 / 50000000000000000000))
    (y := (-((36665309260637508203 / 50000000000000000000)))) (u := (960636681306058219 / 2000000000000000000))
  · norm_num [world12080, agent12080, scalar12080, tp12080, tm12080, ep12080, em12080, dsL]
  · norm_num [world12080, agent12080, scalar12080, tp12080, tm12080, ep12080, em12080, dsL]
  · norm_num [world12080, agent12080, scalar12080, tp12080, tm12080, ep12080, em12080, dsL]
  · norm_num [world12080, agent12080, scalar12080, tp12080, tm12080, ep12080, em12080, dsL]
  · norm_num [world12080, agent12080, scalar12080, tp12080, tm12080, ep12080, em12080, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12080, agent12080, tp12080, tm12080, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12080, agent12080, tp12080, tm12080, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12080, agent12080, scalar12080, tp12080, tm12080, ep12080, em12080, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12080, agent12080, tp12080, tm12080, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12080, agent12080, scalar12080, tp12080, tm12080, ep12080, em12080, dsL]

theorem tails12080 :
    exp (-((12080:ℝ)*ep12080)) ≤ scalar12080.upperTail ∧
    exp (-((12080:ℝ)*em12080)) ≤ scalar12080.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12080:ℝ)) (by norm_num [ep12080]) ?_)
      (show bp12080^8 ≤ scalar12080.upperTail by norm_num [bp12080, scalar12080])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12080, bp12080, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12080:ℝ)) (by norm_num [em12080]) ?_)
      (show bm12080^8 ≤ scalar12080.lowerTail by norm_num [bm12080, scalar12080])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12080, bm12080, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12080 :
    agent12080.root+dsL+scalar12080.worldRadius < √(1/100/aL) ∧
    2*(agent12080.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12080, agent12080, scalar12080, tp12080, tm12080, ep12080, em12080, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12080, agent12080, scalar12080, tp12080, tm12080, ep12080, em12080, dsL]

noncomputable def master12080 : MasterCertificate 12080 world12080 agent12080 :=
  master scalar12080 dsL tp12080 tm12080 ep12080 em12080
    (by norm_num [dsL]) (by norm_num [tp12080]) (by norm_num [tm12080])
    (by norm_num [ep12080]) (by norm_num [em12080])
    positive12080 negative12080 tails12080.1 tails12080.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12080.1 tailGuards12080.2

theorem preserves12080 : master12080.toScalarCertificate = scalar12080 := rfl

noncomputable def tp12081 : ℝ := (47322199 / 200000000)
noncomputable def tm12081 : ℝ := (-((6123720773 / 10000000000)))
noncomputable def ep12081 : ℝ := (27198190154752577 / 50000000000000000000)
noncomputable def em12081 : ℝ := (52465848914322147 / 100000000000000000000)
noncomputable def bp12081 : ℝ := (21989601164666134659 / 50000000000000000000)
noncomputable def bm12081 : ℝ := (9056043932354213029 / 20000000000000000000)

theorem positive12081 :
    Eplus aL (agent12081.root+dsL) scalar12081.worldRadius world12081.frame
      agent12081.frame tp12081 ≤ -ep12081 := by
  apply positive_check (eT := (11620247830939710683 / 10000000000000000000)) (y := (7916618807975093463 / 20000000000000000000)) (u := (148561813830979122517 / 100000000000000000000))
  · norm_num [world12081, agent12081, scalar12081, tp12081, tm12081, ep12081, em12081, dsL]
  · norm_num [world12081, agent12081, scalar12081, tp12081, tm12081, ep12081, em12081, dsL]
  · norm_num [world12081, agent12081, scalar12081, tp12081, tm12081, ep12081, em12081, dsL]
  · norm_num [world12081, agent12081, scalar12081, tp12081, tm12081, ep12081, em12081, dsL]
  · norm_num [world12081, agent12081, scalar12081, tp12081, tm12081, ep12081, em12081, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12081, agent12081, tp12081, tm12081, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12081, agent12081, scalar12081, tp12081, tm12081, ep12081, em12081, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12081, agent12081, tp12081, tm12081, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12081, agent12081, scalar12081, tp12081, tm12081, ep12081, em12081, dsL]

theorem negative12081 :
    Eminus aL (agent12081.root+dsL) scalar12081.worldRadius world12081.frame
      agent12081.frame tm12081 ≤ -em12081 := by
  apply negative_check (lo := (33898952873079625471 / 50000000000000000000)) (hi := (67797905746159250943 / 100000000000000000000))
    (y := (-((36665121371768898657 / 50000000000000000000)))) (u := (2401600727929061647 / 5000000000000000000))
  · norm_num [world12081, agent12081, scalar12081, tp12081, tm12081, ep12081, em12081, dsL]
  · norm_num [world12081, agent12081, scalar12081, tp12081, tm12081, ep12081, em12081, dsL]
  · norm_num [world12081, agent12081, scalar12081, tp12081, tm12081, ep12081, em12081, dsL]
  · norm_num [world12081, agent12081, scalar12081, tp12081, tm12081, ep12081, em12081, dsL]
  · norm_num [world12081, agent12081, scalar12081, tp12081, tm12081, ep12081, em12081, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12081, agent12081, tp12081, tm12081, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12081, agent12081, tp12081, tm12081, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12081, agent12081, scalar12081, tp12081, tm12081, ep12081, em12081, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12081, agent12081, tp12081, tm12081, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12081, agent12081, scalar12081, tp12081, tm12081, ep12081, em12081, dsL]

theorem tails12081 :
    exp (-((12081:ℝ)*ep12081)) ≤ scalar12081.upperTail ∧
    exp (-((12081:ℝ)*em12081)) ≤ scalar12081.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12081:ℝ)) (by norm_num [ep12081]) ?_)
      (show bp12081^8 ≤ scalar12081.upperTail by norm_num [bp12081, scalar12081])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12081, bp12081, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12081:ℝ)) (by norm_num [em12081]) ?_)
      (show bm12081^8 ≤ scalar12081.lowerTail by norm_num [bm12081, scalar12081])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12081, bm12081, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12081 :
    agent12081.root+dsL+scalar12081.worldRadius < √(1/100/aL) ∧
    2*(agent12081.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12081, agent12081, scalar12081, tp12081, tm12081, ep12081, em12081, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12081, agent12081, scalar12081, tp12081, tm12081, ep12081, em12081, dsL]

noncomputable def master12081 : MasterCertificate 12081 world12081 agent12081 :=
  master scalar12081 dsL tp12081 tm12081 ep12081 em12081
    (by norm_num [dsL]) (by norm_num [tp12081]) (by norm_num [tm12081])
    (by norm_num [ep12081]) (by norm_num [em12081])
    positive12081 negative12081 tails12081.1 tails12081.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12081.1 tailGuards12081.2

theorem preserves12081 : master12081.toScalarCertificate = scalar12081 := rfl

noncomputable def tp12082 : ℝ := (2366211381 / 10000000000)
noncomputable def tm12082 : ℝ := (-((6123948819 / 10000000000)))
noncomputable def ep12082 : ℝ := (10879873739630793 / 20000000000000000000)
noncomputable def em12082 : ℝ := (52468451000334601 / 100000000000000000000)
noncomputable def bp12082 : ℝ := (5496778418559283703 / 12500000000000000000)
noncomputable def bm12082 : ℝ := (45275470907092855557 / 100000000000000000000)

theorem positive12082 :
    Eplus aL (agent12082.root+dsL) scalar12082.worldRadius world12082.frame
      agent12082.frame tp12082 ≤ -ep12082 := by
  apply positive_check (eT := (5810140235272451233 / 5000000000000000000)) (y := (19791872999737111847 / 50000000000000000000)) (u := (14856278239714180677 / 10000000000000000000))
  · norm_num [world12082, agent12082, scalar12082, tp12082, tm12082, ep12082, em12082, dsL]
  · norm_num [world12082, agent12082, scalar12082, tp12082, tm12082, ep12082, em12082, dsL]
  · norm_num [world12082, agent12082, scalar12082, tp12082, tm12082, ep12082, em12082, dsL]
  · norm_num [world12082, agent12082, scalar12082, tp12082, tm12082, ep12082, em12082, dsL]
  · norm_num [world12082, agent12082, scalar12082, tp12082, tm12082, ep12082, em12082, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12082, agent12082, tp12082, tm12082, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12082, agent12082, scalar12082, tp12082, tm12082, ep12082, em12082, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12082, agent12082, tp12082, tm12082, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12082, agent12082, scalar12082, tp12082, tm12082, ep12082, em12082, dsL]

theorem negative12082 :
    Eminus aL (agent12082.root+dsL) scalar12082.worldRadius world12082.frame
      agent12082.frame tm12082 ≤ -em12082 := by
  apply negative_check (lo := (2118673787039372847 / 3125000000000000000)) (hi := (13559512237051986221 / 20000000000000000000))
    (y := (-((14665973306616851379 / 20000000000000000000)))) (u := (46906440683965779 / 97656250000000000))
  · norm_num [world12082, agent12082, scalar12082, tp12082, tm12082, ep12082, em12082, dsL]
  · norm_num [world12082, agent12082, scalar12082, tp12082, tm12082, ep12082, em12082, dsL]
  · norm_num [world12082, agent12082, scalar12082, tp12082, tm12082, ep12082, em12082, dsL]
  · norm_num [world12082, agent12082, scalar12082, tp12082, tm12082, ep12082, em12082, dsL]
  · norm_num [world12082, agent12082, scalar12082, tp12082, tm12082, ep12082, em12082, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12082, agent12082, tp12082, tm12082, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12082, agent12082, tp12082, tm12082, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12082, agent12082, scalar12082, tp12082, tm12082, ep12082, em12082, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12082, agent12082, tp12082, tm12082, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12082, agent12082, scalar12082, tp12082, tm12082, ep12082, em12082, dsL]

theorem tails12082 :
    exp (-((12082:ℝ)*ep12082)) ≤ scalar12082.upperTail ∧
    exp (-((12082:ℝ)*em12082)) ≤ scalar12082.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12082:ℝ)) (by norm_num [ep12082]) ?_)
      (show bp12082^8 ≤ scalar12082.upperTail by norm_num [bp12082, scalar12082])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12082, bp12082, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12082:ℝ)) (by norm_num [em12082]) ?_)
      (show bm12082^8 ≤ scalar12082.lowerTail by norm_num [bm12082, scalar12082])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12082, bm12082, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12082 :
    agent12082.root+dsL+scalar12082.worldRadius < √(1/100/aL) ∧
    2*(agent12082.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12082, agent12082, scalar12082, tp12082, tm12082, ep12082, em12082, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12082, agent12082, scalar12082, tp12082, tm12082, ep12082, em12082, dsL]

noncomputable def master12082 : MasterCertificate 12082 world12082 agent12082 :=
  master scalar12082 dsL tp12082 tm12082 ep12082 em12082
    (by norm_num [dsL]) (by norm_num [tp12082]) (by norm_num [tm12082])
    (by norm_num [ep12082]) (by norm_num [em12082])
    positive12082 negative12082 tails12082.1 tails12082.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12082.1 tailGuards12082.2

theorem preserves12082 : master12082.toScalarCertificate = scalar12082 := rfl

noncomputable def tp12083 : ℝ := (2366312837 / 10000000000)
noncomputable def tm12083 : ℝ := (-((6124176707 / 10000000000)))
noncomputable def ep12083 : ℝ := (54402355511608627 / 100000000000000000000)
noncomputable def em12083 : ℝ := (13117762909117901 / 25000000000000000000)
noncomputable def bp12083 : ℝ := (21984626823993253077 / 50000000000000000000)
noncomputable def bm12083 : ℝ := (1810828933892284271 / 4000000000000000000)

theorem positive12083 :
    Eplus aL (agent12083.root+dsL) scalar12083.worldRadius world12083.frame
      agent12083.frame tp12083 ≤ -ep12083 := by
  apply positive_check (eT := (23240626264507158517 / 20000000000000000000)) (y := (3958439905539320919 / 10000000000000000000)) (u := (148563752598353635619 / 100000000000000000000))
  · norm_num [world12083, agent12083, scalar12083, tp12083, tm12083, ep12083, em12083, dsL]
  · norm_num [world12083, agent12083, scalar12083, tp12083, tm12083, ep12083, em12083, dsL]
  · norm_num [world12083, agent12083, scalar12083, tp12083, tm12083, ep12083, em12083, dsL]
  · norm_num [world12083, agent12083, scalar12083, tp12083, tm12083, ep12083, em12083, dsL]
  · norm_num [world12083, agent12083, scalar12083, tp12083, tm12083, ep12083, em12083, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12083, agent12083, tp12083, tm12083, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12083, agent12083, scalar12083, tp12083, tm12083, ep12083, em12083, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12083, agent12083, tp12083, tm12083, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12083, agent12083, scalar12083, tp12083, tm12083, ep12083, em12083, dsL]

theorem negative12083 :
    Eminus aL (agent12083.root+dsL) scalar12083.worldRadius world12083.frame
      agent12083.frame tm12083 ≤ -em12083 := by
  apply negative_check (lo := (33898608622374521373 / 50000000000000000000)) (hi := (67797217244749042747 / 100000000000000000000))
    (y := (-((4583093135348970303 / 6250000000000000000)))) (u := (12008094009573500093 / 25000000000000000000))
  · norm_num [world12083, agent12083, scalar12083, tp12083, tm12083, ep12083, em12083, dsL]
  · norm_num [world12083, agent12083, scalar12083, tp12083, tm12083, ep12083, em12083, dsL]
  · norm_num [world12083, agent12083, scalar12083, tp12083, tm12083, ep12083, em12083, dsL]
  · norm_num [world12083, agent12083, scalar12083, tp12083, tm12083, ep12083, em12083, dsL]
  · norm_num [world12083, agent12083, scalar12083, tp12083, tm12083, ep12083, em12083, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12083, agent12083, tp12083, tm12083, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12083, agent12083, tp12083, tm12083, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12083, agent12083, scalar12083, tp12083, tm12083, ep12083, em12083, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12083, agent12083, tp12083, tm12083, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12083, agent12083, scalar12083, tp12083, tm12083, ep12083, em12083, dsL]

theorem tails12083 :
    exp (-((12083:ℝ)*ep12083)) ≤ scalar12083.upperTail ∧
    exp (-((12083:ℝ)*em12083)) ≤ scalar12083.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12083:ℝ)) (by norm_num [ep12083]) ?_)
      (show bp12083^8 ≤ scalar12083.upperTail by norm_num [bp12083, scalar12083])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12083, bp12083, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12083:ℝ)) (by norm_num [em12083]) ?_)
      (show bm12083^8 ≤ scalar12083.lowerTail by norm_num [bm12083, scalar12083])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12083, bm12083, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12083 :
    agent12083.root+dsL+scalar12083.worldRadius < √(1/100/aL) ∧
    2*(agent12083.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12083, agent12083, scalar12083, tp12083, tm12083, ep12083, em12083, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12083, agent12083, scalar12083, tp12083, tm12083, ep12083, em12083, dsL]

noncomputable def master12083 : MasterCertificate 12083 world12083 agent12083 :=
  master scalar12083 dsL tp12083 tm12083 ep12083 em12083
    (by norm_num [dsL]) (by norm_num [tp12083]) (by norm_num [tm12083])
    (by norm_num [ep12083]) (by norm_num [em12083])
    positive12083 negative12083 tails12083.1 tails12083.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12083.1 tailGuards12083.2

theorem preserves12083 : master12083.toScalarCertificate = scalar12083 := rfl

end BstLean.Part281
