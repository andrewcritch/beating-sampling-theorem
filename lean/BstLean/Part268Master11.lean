import BstLean.Part261Checker
import BstLean.Part268Scalar11
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12625 : ℝ := (2309405219 / 10000000000)
noncomputable def tm12625 : ℝ := (-((755896459 / 1250000000)))
noncomputable def ep12625 : ℝ := (51213337523246611 / 100000000000000000000)
noncomputable def em12625 : ℝ := (49925557095123291 / 100000000000000000000)
noncomputable def bp12625 : ℝ := (5570685751432156223 / 12500000000000000000)
noncomputable def bm12625 : ℝ := (45480446579333099811 / 100000000000000000000)

theorem positive12625 :
    Eplus aL (agent12625.root+dsL) scalar12625.worldRadius world12625.frame
      agent12625.frame tp12625 ≤ -ep12625 := by
  apply positive_check (eT := (57786014872010792149 / 50000000000000000000)) (y := (37806381130554587533 / 100000000000000000000)) (u := (72972803485084368873 / 50000000000000000000))
  · norm_num [world12625, agent12625, scalar12625, tp12625, tm12625, ep12625, em12625, dsL]
  · norm_num [world12625, agent12625, scalar12625, tp12625, tm12625, ep12625, em12625, dsL]
  · norm_num [world12625, agent12625, scalar12625, tp12625, tm12625, ep12625, em12625, dsL]
  · norm_num [world12625, agent12625, scalar12625, tp12625, tm12625, ep12625, em12625, dsL]
  · norm_num [world12625, agent12625, scalar12625, tp12625, tm12625, ep12625, em12625, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12625, agent12625, tp12625, tm12625, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12625, agent12625, scalar12625, tp12625, tm12625, ep12625, em12625, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12625, agent12625, tp12625, tm12625, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12625, agent12625, scalar12625, tp12625, tm12625, ep12625, em12625, dsL]

theorem negative12625 :
    Eminus aL (agent12625.root+dsL) scalar12625.worldRadius world12625.frame
      agent12625.frame tm12625 ≤ -em12625 := by
  apply negative_check (lo := (13691475531333281543 / 20000000000000000000)) (hi := (17114344414166601929 / 25000000000000000000))
    (y := (-((14339212509293216453 / 20000000000000000000)))) (u := (12205848222766430917 / 25000000000000000000))
  · norm_num [world12625, agent12625, scalar12625, tp12625, tm12625, ep12625, em12625, dsL]
  · norm_num [world12625, agent12625, scalar12625, tp12625, tm12625, ep12625, em12625, dsL]
  · norm_num [world12625, agent12625, scalar12625, tp12625, tm12625, ep12625, em12625, dsL]
  · norm_num [world12625, agent12625, scalar12625, tp12625, tm12625, ep12625, em12625, dsL]
  · norm_num [world12625, agent12625, scalar12625, tp12625, tm12625, ep12625, em12625, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12625, agent12625, tp12625, tm12625, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12625, agent12625, tp12625, tm12625, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12625, agent12625, scalar12625, tp12625, tm12625, ep12625, em12625, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12625, agent12625, tp12625, tm12625, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12625, agent12625, scalar12625, tp12625, tm12625, ep12625, em12625, dsL]

theorem tails12625 :
    exp (-((12625:ℝ)*ep12625)) ≤ scalar12625.upperTail ∧
    exp (-((12625:ℝ)*em12625)) ≤ scalar12625.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12625:ℝ)) (by norm_num [ep12625]) ?_)
      (show bp12625^8 ≤ scalar12625.upperTail by norm_num [bp12625, scalar12625])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12625, bp12625, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12625:ℝ)) (by norm_num [em12625]) ?_)
      (show bm12625^8 ≤ scalar12625.lowerTail by norm_num [bm12625, scalar12625])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12625, bm12625, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12625 :
    agent12625.root+dsL+scalar12625.worldRadius < √(1/100/aL) ∧
    2*(agent12625.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12625, agent12625, scalar12625, tp12625, tm12625, ep12625, em12625, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12625, agent12625, scalar12625, tp12625, tm12625, ep12625, em12625, dsL]

noncomputable def master12625 : MasterCertificate 12625 world12625 agent12625 :=
  master scalar12625 dsL tp12625 tm12625 ep12625 em12625
    (by norm_num [dsL]) (by norm_num [tp12625]) (by norm_num [tm12625])
    (by norm_num [ep12625]) (by norm_num [em12625])
    positive12625 negative12625 tails12625.1 tails12625.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12625.1 tailGuards12625.2

theorem preserves12625 : master12625.toScalarCertificate = scalar12625 := rfl

noncomputable def tp12626 : ℝ := (2309493117 / 10000000000)
noncomputable def tm12626 : ℝ := (-((6047360493 / 10000000000)))
noncomputable def ep12626 : ℝ := (10243210375277689 / 20000000000000000000)
noncomputable def em12626 : ℝ := (24963945112505619 / 50000000000000000000)
noncomputable def bp12626 : ℝ := (44560724178515638217 / 100000000000000000000)
noncomputable def bm12626 : ℝ := (5684491724766676743 / 12500000000000000000)

theorem positive12626 :
    Eplus aL (agent12626.root+dsL) scalar12626.worldRadius world12626.frame
      agent12626.frame tp12626 ≤ -ep12626 := by
  apply positive_check (eT := (4622891695884270931 / 4000000000000000000)) (y := (18903603208568242739 / 50000000000000000000)) (u := (145946811444650108363 / 100000000000000000000))
  · norm_num [world12626, agent12626, scalar12626, tp12626, tm12626, ep12626, em12626, dsL]
  · norm_num [world12626, agent12626, scalar12626, tp12626, tm12626, ep12626, em12626, dsL]
  · norm_num [world12626, agent12626, scalar12626, tp12626, tm12626, ep12626, em12626, dsL]
  · norm_num [world12626, agent12626, scalar12626, tp12626, tm12626, ep12626, em12626, dsL]
  · norm_num [world12626, agent12626, scalar12626, tp12626, tm12626, ep12626, em12626, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12626, agent12626, tp12626, tm12626, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12626, agent12626, scalar12626, tp12626, tm12626, ep12626, em12626, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12626, agent12626, tp12626, tm12626, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12626, agent12626, scalar12626, tp12626, tm12626, ep12626, em12626, dsL]

theorem negative12626 :
    Eminus aL (agent12626.root+dsL) scalar12626.worldRadius world12626.frame
      agent12626.frame tm12626 ≤ -em12626 := by
  apply negative_check (lo := (68457147619608584789 / 100000000000000000000)) (hi := (6845714761960858479 / 10000000000000000000))
    (y := (-((71696169386798879131 / 100000000000000000000)))) (u := (12205835182004535431 / 25000000000000000000))
  · norm_num [world12626, agent12626, scalar12626, tp12626, tm12626, ep12626, em12626, dsL]
  · norm_num [world12626, agent12626, scalar12626, tp12626, tm12626, ep12626, em12626, dsL]
  · norm_num [world12626, agent12626, scalar12626, tp12626, tm12626, ep12626, em12626, dsL]
  · norm_num [world12626, agent12626, scalar12626, tp12626, tm12626, ep12626, em12626, dsL]
  · norm_num [world12626, agent12626, scalar12626, tp12626, tm12626, ep12626, em12626, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12626, agent12626, tp12626, tm12626, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12626, agent12626, tp12626, tm12626, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12626, agent12626, scalar12626, tp12626, tm12626, ep12626, em12626, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12626, agent12626, tp12626, tm12626, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12626, agent12626, scalar12626, tp12626, tm12626, ep12626, em12626, dsL]

theorem tails12626 :
    exp (-((12626:ℝ)*ep12626)) ≤ scalar12626.upperTail ∧
    exp (-((12626:ℝ)*em12626)) ≤ scalar12626.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12626:ℝ)) (by norm_num [ep12626]) ?_)
      (show bp12626^8 ≤ scalar12626.upperTail by norm_num [bp12626, scalar12626])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12626, bp12626, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12626:ℝ)) (by norm_num [em12626]) ?_)
      (show bm12626^8 ≤ scalar12626.lowerTail by norm_num [bm12626, scalar12626])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12626, bm12626, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12626 :
    agent12626.root+dsL+scalar12626.worldRadius < √(1/100/aL) ∧
    2*(agent12626.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12626, agent12626, scalar12626, tp12626, tm12626, ep12626, em12626, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12626, agent12626, scalar12626, tp12626, tm12626, ep12626, em12626, dsL]

noncomputable def master12626 : MasterCertificate 12626 world12626 agent12626 :=
  master scalar12626 dsL tp12626 tm12626 ep12626 em12626
    (by norm_num [dsL]) (by norm_num [tp12626]) (by norm_num [tm12626])
    (by norm_num [ep12626]) (by norm_num [em12626])
    positive12626 negative12626 tails12626.1 tails12626.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12626.1 tailGuards12626.2

theorem preserves12626 : master12626.toScalarCertificate = scalar12626 := rfl

noncomputable def tp12627 : ℝ := (577395253 / 2500000000)
noncomputable def tm12627 : ℝ := (-((755943667 / 1250000000)))
noncomputable def ep12627 : ℝ := (25609382697174423 / 50000000000000000000)
noncomputable def em12627 : ℝ := (49930222590487741 / 100000000000000000000)
noncomputable def bp12627 : ℝ := (11138990784843831659 / 25000000000000000000)
noncomputable def bm12627 : ℝ := (9094284349622281197 / 20000000000000000000)

theorem positive12627 :
    Eplus aL (agent12627.root+dsL) scalar12627.worldRadius world12627.frame
      agent12627.frame tp12627 ≤ -ep12627 := by
  apply positive_check (eT := (115572555061001880587 / 100000000000000000000)) (y := (37808031933619672889 / 100000000000000000000)) (u := (9121751016538016077 / 6250000000000000000))
  · norm_num [world12627, agent12627, scalar12627, tp12627, tm12627, ep12627, em12627, dsL]
  · norm_num [world12627, agent12627, scalar12627, tp12627, tm12627, ep12627, em12627, dsL]
  · norm_num [world12627, agent12627, scalar12627, tp12627, tm12627, ep12627, em12627, dsL]
  · norm_num [world12627, agent12627, scalar12627, tp12627, tm12627, ep12627, em12627, dsL]
  · norm_num [world12627, agent12627, scalar12627, tp12627, tm12627, ep12627, em12627, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12627, agent12627, tp12627, tm12627, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12627, agent12627, scalar12627, tp12627, tm12627, ep12627, em12627, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12627, agent12627, tp12627, tm12627, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12627, agent12627, scalar12627, tp12627, tm12627, ep12627, em12627, dsL]

theorem negative12627 :
    Eminus aL (agent12627.root+dsL) scalar12627.worldRadius world12627.frame
      agent12627.frame tm12627 ≤ -em12627 := by
  apply negative_check (lo := (34228458715740225223 / 50000000000000000000)) (hi := (68456917431480450447 / 100000000000000000000))
    (y := (-((17924069289606734509 / 25000000000000000000)))) (u := (48823288110337319863 / 100000000000000000000))
  · norm_num [world12627, agent12627, scalar12627, tp12627, tm12627, ep12627, em12627, dsL]
  · norm_num [world12627, agent12627, scalar12627, tp12627, tm12627, ep12627, em12627, dsL]
  · norm_num [world12627, agent12627, scalar12627, tp12627, tm12627, ep12627, em12627, dsL]
  · norm_num [world12627, agent12627, scalar12627, tp12627, tm12627, ep12627, em12627, dsL]
  · norm_num [world12627, agent12627, scalar12627, tp12627, tm12627, ep12627, em12627, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12627, agent12627, tp12627, tm12627, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12627, agent12627, tp12627, tm12627, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12627, agent12627, scalar12627, tp12627, tm12627, ep12627, em12627, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12627, agent12627, tp12627, tm12627, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12627, agent12627, scalar12627, tp12627, tm12627, ep12627, em12627, dsL]

theorem tails12627 :
    exp (-((12627:ℝ)*ep12627)) ≤ scalar12627.upperTail ∧
    exp (-((12627:ℝ)*em12627)) ≤ scalar12627.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12627:ℝ)) (by norm_num [ep12627]) ?_)
      (show bp12627^8 ≤ scalar12627.upperTail by norm_num [bp12627, scalar12627])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12627, bp12627, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12627:ℝ)) (by norm_num [em12627]) ?_)
      (show bm12627^8 ≤ scalar12627.lowerTail by norm_num [bm12627, scalar12627])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12627, bm12627, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12627 :
    agent12627.root+dsL+scalar12627.worldRadius < √(1/100/aL) ∧
    2*(agent12627.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12627, agent12627, scalar12627, tp12627, tm12627, ep12627, em12627, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12627, agent12627, scalar12627, tp12627, tm12627, ep12627, em12627, dsL]

noncomputable def master12627 : MasterCertificate 12627 world12627 agent12627 :=
  master scalar12627 dsL tp12627 tm12627 ep12627 em12627
    (by norm_num [dsL]) (by norm_num [tp12627]) (by norm_num [tm12627])
    (by norm_num [ep12627]) (by norm_num [em12627])
    positive12627 negative12627 tails12627.1 tails12627.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12627.1 tailGuards12627.2

theorem preserves12627 : master12627.toScalarCertificate = scalar12627 := rfl

noncomputable def tp12628 : ℝ := (2309668791 / 10000000000)
noncomputable def tm12628 : ℝ := (-((6047737981 / 10000000000)))
noncomputable def ep12628 : ℝ := (10244295334902127 / 20000000000000000000)
noncomputable def em12628 : ℝ := (49932552900105407 / 100000000000000000000)
noncomputable def bp12628 : ℝ := (22275601940203840103 / 50000000000000000000)
noncomputable def bm12628 : ℝ := (710420489939596923 / 1562500000000000000)

theorem positive12628 :
    Eplus aL (agent12628.root+dsL) scalar12628.worldRadius world12628.frame
      agent12628.frame tp12628 ≤ -ep12628 := by
  apply positive_check (eT := (5778640845869064373 / 5000000000000000000)) (y := (37808855941424978763 / 100000000000000000000)) (u := (145949218892608834183 / 100000000000000000000))
  · norm_num [world12628, agent12628, scalar12628, tp12628, tm12628, ep12628, em12628, dsL]
  · norm_num [world12628, agent12628, scalar12628, tp12628, tm12628, ep12628, em12628, dsL]
  · norm_num [world12628, agent12628, scalar12628, tp12628, tm12628, ep12628, em12628, dsL]
  · norm_num [world12628, agent12628, scalar12628, tp12628, tm12628, ep12628, em12628, dsL]
  · norm_num [world12628, agent12628, scalar12628, tp12628, tm12628, ep12628, em12628, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12628, agent12628, tp12628, tm12628, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12628, agent12628, scalar12628, tp12628, tm12628, ep12628, em12628, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12628, agent12628, tp12628, tm12628, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12628, agent12628, scalar12628, tp12628, tm12628, ep12628, em12628, dsL]

theorem negative12628 :
    Eminus aL (agent12628.root+dsL) scalar12628.worldRadius world12628.frame
      agent12628.frame tm12628 ≤ -em12628 := by
  apply negative_check (lo := (17114172008993204641 / 25000000000000000000)) (hi := (13691337607194563713 / 20000000000000000000))
    (y := (-((35848191871886132363 / 50000000000000000000)))) (u := (48823236071894820297 / 100000000000000000000))
  · norm_num [world12628, agent12628, scalar12628, tp12628, tm12628, ep12628, em12628, dsL]
  · norm_num [world12628, agent12628, scalar12628, tp12628, tm12628, ep12628, em12628, dsL]
  · norm_num [world12628, agent12628, scalar12628, tp12628, tm12628, ep12628, em12628, dsL]
  · norm_num [world12628, agent12628, scalar12628, tp12628, tm12628, ep12628, em12628, dsL]
  · norm_num [world12628, agent12628, scalar12628, tp12628, tm12628, ep12628, em12628, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12628, agent12628, tp12628, tm12628, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12628, agent12628, tp12628, tm12628, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12628, agent12628, scalar12628, tp12628, tm12628, ep12628, em12628, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12628, agent12628, tp12628, tm12628, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12628, agent12628, scalar12628, tp12628, tm12628, ep12628, em12628, dsL]

theorem tails12628 :
    exp (-((12628:ℝ)*ep12628)) ≤ scalar12628.upperTail ∧
    exp (-((12628:ℝ)*em12628)) ≤ scalar12628.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12628:ℝ)) (by norm_num [ep12628]) ?_)
      (show bp12628^8 ≤ scalar12628.upperTail by norm_num [bp12628, scalar12628])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12628, bp12628, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12628:ℝ)) (by norm_num [em12628]) ?_)
      (show bm12628^8 ≤ scalar12628.lowerTail by norm_num [bm12628, scalar12628])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12628, bm12628, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12628 :
    agent12628.root+dsL+scalar12628.worldRadius < √(1/100/aL) ∧
    2*(agent12628.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12628, agent12628, scalar12628, tp12628, tm12628, ep12628, em12628, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12628, agent12628, scalar12628, tp12628, tm12628, ep12628, em12628, dsL]

noncomputable def master12628 : MasterCertificate 12628 world12628 agent12628 :=
  master scalar12628 dsL tp12628 tm12628 ep12628 em12628
    (by norm_num [dsL]) (by norm_num [tp12628]) (by norm_num [tm12628])
    (by norm_num [ep12628]) (by norm_num [em12628])
    positive12628 negative12628 tails12628.1 tails12628.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12628.1 tailGuards12628.2

theorem preserves12628 : master12628.toScalarCertificate = scalar12628 := rfl

noncomputable def tp12629 : ℝ := (577439133 / 2500000000)
noncomputable def tm12629 : ℝ := (-((3023963287 / 5000000000)))
noncomputable def ep12629 : ℝ := (10244837486181871 / 20000000000000000000)
noncomputable def em12629 : ℝ := (49934882711024501 / 100000000000000000000)
noncomputable def bp12629 : ℝ := (44546445196178374813 / 100000000000000000000)
noncomputable def bm12629 : ℝ := (22731200752301804481 / 50000000000000000000)

theorem positive12629 :
    Eplus aL (agent12629.root+dsL) scalar12629.worldRadius world12629.frame
      agent12629.frame tp12629 ≤ -ep12629 := by
  apply positive_check (eT := (4622923141244966323 / 4000000000000000000)) (y := (9452419891089251977 / 25000000000000000000)) (u := (36487605242198757973 / 25000000000000000000))
  · norm_num [world12629, agent12629, scalar12629, tp12629, tm12629, ep12629, em12629, dsL]
  · norm_num [world12629, agent12629, scalar12629, tp12629, tm12629, ep12629, em12629, dsL]
  · norm_num [world12629, agent12629, scalar12629, tp12629, tm12629, ep12629, em12629, dsL]
  · norm_num [world12629, agent12629, scalar12629, tp12629, tm12629, ep12629, em12629, dsL]
  · norm_num [world12629, agent12629, scalar12629, tp12629, tm12629, ep12629, em12629, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12629, agent12629, tp12629, tm12629, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12629, agent12629, scalar12629, tp12629, tm12629, ep12629, em12629, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12629, agent12629, tp12629, tm12629, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12629, agent12629, scalar12629, tp12629, tm12629, ep12629, em12629, dsL]

theorem negative12629 :
    Eminus aL (agent12629.root+dsL) scalar12629.worldRadius world12629.frame
      agent12629.frame tm12629 ≤ -em12629 := by
  apply negative_check (lo := (684564588068152683 / 1000000000000000000)) (hi := (68456458806815268301 / 100000000000000000000))
    (y := (-((35848245270695910881 / 50000000000000000000)))) (u := (48823183929868748027 / 100000000000000000000))
  · norm_num [world12629, agent12629, scalar12629, tp12629, tm12629, ep12629, em12629, dsL]
  · norm_num [world12629, agent12629, scalar12629, tp12629, tm12629, ep12629, em12629, dsL]
  · norm_num [world12629, agent12629, scalar12629, tp12629, tm12629, ep12629, em12629, dsL]
  · norm_num [world12629, agent12629, scalar12629, tp12629, tm12629, ep12629, em12629, dsL]
  · norm_num [world12629, agent12629, scalar12629, tp12629, tm12629, ep12629, em12629, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12629, agent12629, tp12629, tm12629, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12629, agent12629, tp12629, tm12629, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12629, agent12629, scalar12629, tp12629, tm12629, ep12629, em12629, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12629, agent12629, tp12629, tm12629, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12629, agent12629, scalar12629, tp12629, tm12629, ep12629, em12629, dsL]

theorem tails12629 :
    exp (-((12629:ℝ)*ep12629)) ≤ scalar12629.upperTail ∧
    exp (-((12629:ℝ)*em12629)) ≤ scalar12629.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12629:ℝ)) (by norm_num [ep12629]) ?_)
      (show bp12629^8 ≤ scalar12629.upperTail by norm_num [bp12629, scalar12629])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12629, bp12629, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12629:ℝ)) (by norm_num [em12629]) ?_)
      (show bm12629^8 ≤ scalar12629.lowerTail by norm_num [bm12629, scalar12629])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12629, bm12629, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12629 :
    agent12629.root+dsL+scalar12629.worldRadius < √(1/100/aL) ∧
    2*(agent12629.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12629, agent12629, scalar12629, tp12629, tm12629, ep12629, em12629, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12629, agent12629, scalar12629, tp12629, tm12629, ep12629, em12629, dsL]

noncomputable def master12629 : MasterCertificate 12629 world12629 agent12629 :=
  master scalar12629 dsL tp12629 tm12629 ep12629 em12629
    (by norm_num [dsL]) (by norm_num [tp12629]) (by norm_num [tm12629])
    (by norm_num [ep12629]) (by norm_num [em12629])
    positive12629 negative12629 tails12629.1 tails12629.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12629.1 tailGuards12629.2

theorem preserves12629 : master12629.toScalarCertificate = scalar12629 := rfl

noncomputable def tp12630 : ℝ := (2309919281 / 10000000000)
noncomputable def tm12630 : ℝ := (-((3024170903 / 5000000000)))
noncomputable def ep12630 : ℝ := (51228332674422647 / 100000000000000000000)
noncomputable def em12630 : ℝ := (6242346850233829 / 12500000000000000000)
noncomputable def bp12630 : ℝ := (11135169498943995291 / 25000000000000000000)
noncomputable def bm12630 : ℝ := (5682096331692977399 / 12500000000000000000)

theorem positive12630 :
    Eplus aL (agent12630.root+dsL) scalar12630.worldRadius world12630.frame
      agent12630.frame tp12630 ≤ -ep12630 := by
  apply positive_check (eT := (288934708436547437 / 250000000000000000)) (y := (37809776311317559037 / 100000000000000000000)) (u := (145950562171459535411 / 100000000000000000000))
  · norm_num [world12630, agent12630, scalar12630, tp12630, tm12630, ep12630, em12630, dsL]
  · norm_num [world12630, agent12630, scalar12630, tp12630, tm12630, ep12630, em12630, dsL]
  · norm_num [world12630, agent12630, scalar12630, tp12630, tm12630, ep12630, em12630, dsL]
  · norm_num [world12630, agent12630, scalar12630, tp12630, tm12630, ep12630, em12630, dsL]
  · norm_num [world12630, agent12630, scalar12630, tp12630, tm12630, ep12630, em12630, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12630, agent12630, tp12630, tm12630, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12630, agent12630, scalar12630, tp12630, tm12630, ep12630, em12630, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12630, agent12630, tp12630, tm12630, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12630, agent12630, scalar12630, tp12630, tm12630, ep12630, em12630, dsL]

theorem negative12630 :
    Eminus aL (agent12630.root+dsL) scalar12630.worldRadius world12630.frame
      agent12630.frame tm12630 ≤ -em12630 := by
  apply negative_check (lo := (34227628682680819761 / 50000000000000000000)) (hi := (68455257365361639523 / 100000000000000000000))
    (y := (-((14338936311669008501 / 20000000000000000000)))) (u := (24412033570488741367 / 50000000000000000000))
  · norm_num [world12630, agent12630, scalar12630, tp12630, tm12630, ep12630, em12630, dsL]
  · norm_num [world12630, agent12630, scalar12630, tp12630, tm12630, ep12630, em12630, dsL]
  · norm_num [world12630, agent12630, scalar12630, tp12630, tm12630, ep12630, em12630, dsL]
  · norm_num [world12630, agent12630, scalar12630, tp12630, tm12630, ep12630, em12630, dsL]
  · norm_num [world12630, agent12630, scalar12630, tp12630, tm12630, ep12630, em12630, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12630, agent12630, tp12630, tm12630, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12630, agent12630, tp12630, tm12630, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12630, agent12630, scalar12630, tp12630, tm12630, ep12630, em12630, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12630, agent12630, tp12630, tm12630, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12630, agent12630, scalar12630, tp12630, tm12630, ep12630, em12630, dsL]

theorem tails12630 :
    exp (-((12630:ℝ)*ep12630)) ≤ scalar12630.upperTail ∧
    exp (-((12630:ℝ)*em12630)) ≤ scalar12630.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12630:ℝ)) (by norm_num [ep12630]) ?_)
      (show bp12630^8 ≤ scalar12630.upperTail by norm_num [bp12630, scalar12630])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12630, bp12630, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12630:ℝ)) (by norm_num [em12630]) ?_)
      (show bm12630^8 ≤ scalar12630.lowerTail by norm_num [bm12630, scalar12630])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12630, bm12630, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12630 :
    agent12630.root+dsL+scalar12630.worldRadius < √(1/100/aL) ∧
    2*(agent12630.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12630, agent12630, scalar12630, tp12630, tm12630, ep12630, em12630, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12630, agent12630, scalar12630, tp12630, tm12630, ep12630, em12630, dsL]

noncomputable def master12630 : MasterCertificate 12630 world12630 agent12630 :=
  master scalar12630 dsL tp12630 tm12630 ep12630 em12630
    (by norm_num [dsL]) (by norm_num [tp12630]) (by norm_num [tm12630])
    (by norm_num [ep12630]) (by norm_num [em12630])
    positive12630 negative12630 tails12630.1 tails12630.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12630.1 tailGuards12630.2

theorem preserves12630 : master12630.toScalarCertificate = scalar12630 := rfl

noncomputable def tp12631 : ℝ := (2310006927 / 10000000000)
noncomputable def tm12631 : ℝ := (-((3024265093 / 5000000000)))
noncomputable def ep12631 : ℝ := (51231039841928779 / 100000000000000000000)
noncomputable def em12631 : ℝ := (12485275324247949 / 25000000000000000000)
noncomputable def bp12631 : ℝ := (44535922275957828041 / 100000000000000000000)
noncomputable def bm12631 : ℝ := (22726131784580166927 / 50000000000000000000)

theorem positive12631 :
    Eplus aL (agent12631.root+dsL) scalar12631.worldRadius world12631.frame
      agent12631.frame tp12631 ≤ -ep12631 := by
  apply positive_check (eT := (57787072177326505679 / 50000000000000000000)) (y := (18905299544608354253 / 50000000000000000000)) (u := (29190352605073788019 / 20000000000000000000))
  · norm_num [world12631, agent12631, scalar12631, tp12631, tm12631, ep12631, em12631, dsL]
  · norm_num [world12631, agent12631, scalar12631, tp12631, tm12631, ep12631, em12631, dsL]
  · norm_num [world12631, agent12631, scalar12631, tp12631, tm12631, ep12631, em12631, dsL]
  · norm_num [world12631, agent12631, scalar12631, tp12631, tm12631, ep12631, em12631, dsL]
  · norm_num [world12631, agent12631, scalar12631, tp12631, tm12631, ep12631, em12631, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12631, agent12631, tp12631, tm12631, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12631, agent12631, scalar12631, tp12631, tm12631, ep12631, em12631, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12631, agent12631, tp12631, tm12631, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12631, agent12631, scalar12631, tp12631, tm12631, ep12631, em12631, dsL]

theorem negative12631 :
    Eminus aL (agent12631.root+dsL) scalar12631.worldRadius world12631.frame
      agent12631.frame tm12631 ≤ -em12631 := by
  apply negative_check (lo := (68455028961337556447 / 100000000000000000000)) (hi := (2139219655041798639 / 3125000000000000000))
    (y := (-((71694787368894830351 / 100000000000000000000)))) (u := (48824015479990943471 / 100000000000000000000))
  · norm_num [world12631, agent12631, scalar12631, tp12631, tm12631, ep12631, em12631, dsL]
  · norm_num [world12631, agent12631, scalar12631, tp12631, tm12631, ep12631, em12631, dsL]
  · norm_num [world12631, agent12631, scalar12631, tp12631, tm12631, ep12631, em12631, dsL]
  · norm_num [world12631, agent12631, scalar12631, tp12631, tm12631, ep12631, em12631, dsL]
  · norm_num [world12631, agent12631, scalar12631, tp12631, tm12631, ep12631, em12631, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12631, agent12631, tp12631, tm12631, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12631, agent12631, tp12631, tm12631, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12631, agent12631, scalar12631, tp12631, tm12631, ep12631, em12631, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12631, agent12631, tp12631, tm12631, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12631, agent12631, scalar12631, tp12631, tm12631, ep12631, em12631, dsL]

theorem tails12631 :
    exp (-((12631:ℝ)*ep12631)) ≤ scalar12631.upperTail ∧
    exp (-((12631:ℝ)*em12631)) ≤ scalar12631.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12631:ℝ)) (by norm_num [ep12631]) ?_)
      (show bp12631^8 ≤ scalar12631.upperTail by norm_num [bp12631, scalar12631])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12631, bp12631, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12631:ℝ)) (by norm_num [em12631]) ?_)
      (show bm12631^8 ≤ scalar12631.lowerTail by norm_num [bm12631, scalar12631])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12631, bm12631, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12631 :
    agent12631.root+dsL+scalar12631.worldRadius < √(1/100/aL) ∧
    2*(agent12631.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12631, agent12631, scalar12631, tp12631, tm12631, ep12631, em12631, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12631, agent12631, scalar12631, tp12631, tm12631, ep12631, em12631, dsL]

noncomputable def master12631 : MasterCertificate 12631 world12631 agent12631 :=
  master scalar12631 dsL tp12631 tm12631 ep12631 em12631
    (by norm_num [dsL]) (by norm_num [tp12631]) (by norm_num [tm12631])
    (by norm_num [ep12631]) (by norm_num [em12631])
    positive12631 negative12631 tails12631.1 tails12631.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12631.1 tailGuards12631.2

theorem preserves12631 : master12631.toScalarCertificate = scalar12631 := rfl

noncomputable def tp12632 : ℝ := (144380913 / 625000000)
noncomputable def tm12632 : ℝ := (-((1512179667 / 2500000000)))
noncomputable def ep12632 : ℝ := (25616873328774881 / 50000000000000000000)
noncomputable def em12632 : ℝ := (49943427480958009 / 100000000000000000000)
noncomputable def bp12632 : ℝ := (5566395876245438683 / 12500000000000000000)
noncomputable def bm12632 : ℝ := (710121201415857239 / 1562500000000000000)

theorem positive12632 :
    Eplus aL (agent12632.root+dsL) scalar12632.worldRadius world12632.frame
      agent12632.frame tp12632 ≤ -ep12632 := by
  apply positive_check (eT := (115574405620709974673 / 100000000000000000000)) (y := (37811422817135972671 / 100000000000000000000)) (u := (145952965275741267521 / 100000000000000000000))
  · norm_num [world12632, agent12632, scalar12632, tp12632, tm12632, ep12632, em12632, dsL]
  · norm_num [world12632, agent12632, scalar12632, tp12632, tm12632, ep12632, em12632, dsL]
  · norm_num [world12632, agent12632, scalar12632, tp12632, tm12632, ep12632, em12632, dsL]
  · norm_num [world12632, agent12632, scalar12632, tp12632, tm12632, ep12632, em12632, dsL]
  · norm_num [world12632, agent12632, scalar12632, tp12632, tm12632, ep12632, em12632, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12632, agent12632, tp12632, tm12632, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12632, agent12632, scalar12632, tp12632, tm12632, ep12632, em12632, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12632, agent12632, tp12632, tm12632, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12632, agent12632, scalar12632, tp12632, tm12632, ep12632, em12632, dsL]

theorem negative12632 :
    Eminus aL (agent12632.root+dsL) scalar12632.worldRadius world12632.frame
      agent12632.frame tm12632 ≤ -em12632 := by
  apply negative_check (lo := (68454800063104270947 / 100000000000000000000)) (hi := (17113700015776067737 / 25000000000000000000))
    (y := (-((35847447714717385767 / 50000000000000000000)))) (u := (48823962720524700913 / 100000000000000000000))
  · norm_num [world12632, agent12632, scalar12632, tp12632, tm12632, ep12632, em12632, dsL]
  · norm_num [world12632, agent12632, scalar12632, tp12632, tm12632, ep12632, em12632, dsL]
  · norm_num [world12632, agent12632, scalar12632, tp12632, tm12632, ep12632, em12632, dsL]
  · norm_num [world12632, agent12632, scalar12632, tp12632, tm12632, ep12632, em12632, dsL]
  · norm_num [world12632, agent12632, scalar12632, tp12632, tm12632, ep12632, em12632, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12632, agent12632, tp12632, tm12632, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12632, agent12632, tp12632, tm12632, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12632, agent12632, scalar12632, tp12632, tm12632, ep12632, em12632, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12632, agent12632, tp12632, tm12632, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12632, agent12632, scalar12632, tp12632, tm12632, ep12632, em12632, dsL]

theorem tails12632 :
    exp (-((12632:ℝ)*ep12632)) ≤ scalar12632.upperTail ∧
    exp (-((12632:ℝ)*em12632)) ≤ scalar12632.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12632:ℝ)) (by norm_num [ep12632]) ?_)
      (show bp12632^8 ≤ scalar12632.upperTail by norm_num [bp12632, scalar12632])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12632, bp12632, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12632:ℝ)) (by norm_num [em12632]) ?_)
      (show bm12632^8 ≤ scalar12632.lowerTail by norm_num [bm12632, scalar12632])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12632, bm12632, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12632 :
    agent12632.root+dsL+scalar12632.worldRadius < √(1/100/aL) ∧
    2*(agent12632.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12632, agent12632, scalar12632, tp12632, tm12632, ep12632, em12632, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12632, agent12632, scalar12632, tp12632, tm12632, ep12632, em12632, dsL]

noncomputable def master12632 : MasterCertificate 12632 world12632 agent12632 :=
  master scalar12632 dsL tp12632 tm12632 ep12632 em12632
    (by norm_num [dsL]) (by norm_num [tp12632]) (by norm_num [tm12632])
    (by norm_num [ep12632]) (by norm_num [em12632])
    positive12632 negative12632 tails12632.1 tails12632.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12632.1 tailGuards12632.2

theorem preserves12632 : master12632.toScalarCertificate = scalar12632 := rfl

noncomputable def tp12633 : ℝ := (577545543 / 2500000000)
noncomputable def tm12633 : ℝ := (-((6048906723 / 10000000000)))
noncomputable def ep12633 : ℝ := (10247290186290781 / 20000000000000000000)
noncomputable def em12633 : ℝ := (12486437820515979 / 25000000000000000000)
noncomputable def bp12633 : ℝ := (445264137375462089 / 1000000000000000000)
noncomputable def bm12633 : ℝ := (9088650420919198549 / 20000000000000000000)

theorem positive12633 :
    Eplus aL (agent12633.root+dsL) scalar12633.worldRadius world12633.frame
      agent12633.frame tp12633 ≤ -ep12633 := by
  apply positive_check (eT := (115574666072109912789 / 100000000000000000000)) (y := (3781224511781823439 / 10000000000000000000)) (u := (36488541363226259223 / 25000000000000000000))
  · norm_num [world12633, agent12633, scalar12633, tp12633, tm12633, ep12633, em12633, dsL]
  · norm_num [world12633, agent12633, scalar12633, tp12633, tm12633, ep12633, em12633, dsL]
  · norm_num [world12633, agent12633, scalar12633, tp12633, tm12633, ep12633, em12633, dsL]
  · norm_num [world12633, agent12633, scalar12633, tp12633, tm12633, ep12633, em12633, dsL]
  · norm_num [world12633, agent12633, scalar12633, tp12633, tm12633, ep12633, em12633, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12633, agent12633, tp12633, tm12633, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12633, agent12633, scalar12633, tp12633, tm12633, ep12633, em12633, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12633, agent12633, tp12633, tm12633, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12633, agent12633, scalar12633, tp12633, tm12633, ep12633, em12633, dsL]

theorem negative12633 :
    Eminus aL (agent12633.root+dsL) scalar12633.worldRadius world12633.frame
      agent12633.frame tm12633 ≤ -em12633 := by
  apply negative_check (lo := (17113643234892880059 / 25000000000000000000)) (hi := (68454572939571520237 / 100000000000000000000))
    (y := (-((71694999819947055753 / 100000000000000000000)))) (u := (48823911752966502153 / 100000000000000000000))
  · norm_num [world12633, agent12633, scalar12633, tp12633, tm12633, ep12633, em12633, dsL]
  · norm_num [world12633, agent12633, scalar12633, tp12633, tm12633, ep12633, em12633, dsL]
  · norm_num [world12633, agent12633, scalar12633, tp12633, tm12633, ep12633, em12633, dsL]
  · norm_num [world12633, agent12633, scalar12633, tp12633, tm12633, ep12633, em12633, dsL]
  · norm_num [world12633, agent12633, scalar12633, tp12633, tm12633, ep12633, em12633, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12633, agent12633, tp12633, tm12633, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12633, agent12633, tp12633, tm12633, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12633, agent12633, scalar12633, tp12633, tm12633, ep12633, em12633, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12633, agent12633, tp12633, tm12633, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12633, agent12633, scalar12633, tp12633, tm12633, ep12633, em12633, dsL]

theorem tails12633 :
    exp (-((12633:ℝ)*ep12633)) ≤ scalar12633.upperTail ∧
    exp (-((12633:ℝ)*em12633)) ≤ scalar12633.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12633:ℝ)) (by norm_num [ep12633]) ?_)
      (show bp12633^8 ≤ scalar12633.upperTail by norm_num [bp12633, scalar12633])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12633, bp12633, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12633:ℝ)) (by norm_num [em12633]) ?_)
      (show bm12633^8 ≤ scalar12633.lowerTail by norm_num [bm12633, scalar12633])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12633, bm12633, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12633 :
    agent12633.root+dsL+scalar12633.worldRadius < √(1/100/aL) ∧
    2*(agent12633.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12633, agent12633, scalar12633, tp12633, tm12633, ep12633, em12633, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12633, agent12633, scalar12633, tp12633, tm12633, ep12633, em12633, dsL]

noncomputable def master12633 : MasterCertificate 12633 world12633 agent12633 :=
  master scalar12633 dsL tp12633 tm12633 ep12633 em12633
    (by norm_num [dsL]) (by norm_num [tp12633]) (by norm_num [tm12633])
    (by norm_num [ep12633]) (by norm_num [em12633])
    positive12633 negative12633 tails12633.1 tails12633.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12633.1 tailGuards12633.2

theorem preserves12633 : master12633.toScalarCertificate = scalar12633 := rfl

noncomputable def tp12634 : ℝ := (92410789 / 400000000)
noncomputable def tm12634 : ℝ := (-((3024547417 / 5000000000)))
noncomputable def ep12634 : ℝ := (51239154370547369 / 100000000000000000000)
noncomputable def em12634 : ℝ := (12487018579856383 / 25000000000000000000)
noncomputable def bp12634 : ℝ := (5565207657307538241 / 12500000000000000000)
noncomputable def bm12634 : ℝ := (45438748049171767671 / 100000000000000000000)

theorem positive12634 :
    Eplus aL (agent12634.root+dsL) scalar12634.worldRadius world12634.frame
      agent12634.frame tp12634 ≤ -ep12634 := by
  apply positive_check (eT := (7223432904778824291 / 6250000000000000000)) (y := (37813067506469522989 / 100000000000000000000)) (u := (72977682884166713367 / 50000000000000000000))
  · norm_num [world12634, agent12634, scalar12634, tp12634, tm12634, ep12634, em12634, dsL]
  · norm_num [world12634, agent12634, scalar12634, tp12634, tm12634, ep12634, em12634, dsL]
  · norm_num [world12634, agent12634, scalar12634, tp12634, tm12634, ep12634, em12634, dsL]
  · norm_num [world12634, agent12634, scalar12634, tp12634, tm12634, ep12634, em12634, dsL]
  · norm_num [world12634, agent12634, scalar12634, tp12634, tm12634, ep12634, em12634, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12634, agent12634, tp12634, tm12634, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12634, agent12634, scalar12634, tp12634, tm12634, ep12634, em12634, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12634, agent12634, tp12634, tm12634, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12634, agent12634, scalar12634, tp12634, tm12634, ep12634, em12634, dsL]

theorem negative12634 :
    Eminus aL (agent12634.root+dsL) scalar12634.worldRadius world12634.frame
      agent12634.frame tm12634 ≤ -em12634 := by
  apply negative_check (lo := (68454345519056951959 / 100000000000000000000)) (hi := (1711358637976423799 / 2500000000000000000))
    (y := (-((7169510547049129421 / 10000000000000000000)))) (u := (48823860170265265347 / 100000000000000000000))
  · norm_num [world12634, agent12634, scalar12634, tp12634, tm12634, ep12634, em12634, dsL]
  · norm_num [world12634, agent12634, scalar12634, tp12634, tm12634, ep12634, em12634, dsL]
  · norm_num [world12634, agent12634, scalar12634, tp12634, tm12634, ep12634, em12634, dsL]
  · norm_num [world12634, agent12634, scalar12634, tp12634, tm12634, ep12634, em12634, dsL]
  · norm_num [world12634, agent12634, scalar12634, tp12634, tm12634, ep12634, em12634, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12634, agent12634, tp12634, tm12634, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12634, agent12634, tp12634, tm12634, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12634, agent12634, scalar12634, tp12634, tm12634, ep12634, em12634, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12634, agent12634, tp12634, tm12634, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12634, agent12634, scalar12634, tp12634, tm12634, ep12634, em12634, dsL]

theorem tails12634 :
    exp (-((12634:ℝ)*ep12634)) ≤ scalar12634.upperTail ∧
    exp (-((12634:ℝ)*em12634)) ≤ scalar12634.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12634:ℝ)) (by norm_num [ep12634]) ?_)
      (show bp12634^8 ≤ scalar12634.upperTail by norm_num [bp12634, scalar12634])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12634, bp12634, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12634:ℝ)) (by norm_num [em12634]) ?_)
      (show bm12634^8 ≤ scalar12634.lowerTail by norm_num [bm12634, scalar12634])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12634, bm12634, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12634 :
    agent12634.root+dsL+scalar12634.worldRadius < √(1/100/aL) ∧
    2*(agent12634.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12634, agent12634, scalar12634, tp12634, tm12634, ep12634, em12634, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12634, agent12634, scalar12634, tp12634, tm12634, ep12634, em12634, dsL]

noncomputable def master12634 : MasterCertificate 12634 world12634 agent12634 :=
  master scalar12634 dsL tp12634 tm12634 ep12634 em12634
    (by norm_num [dsL]) (by norm_num [tp12634]) (by norm_num [tm12634])
    (by norm_num [ep12634]) (by norm_num [em12634])
    positive12634 negative12634 tails12634.1 tails12634.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12634.1 tailGuards12634.2

theorem preserves12634 : master12634.toScalarCertificate = scalar12634 := rfl

noncomputable def tp12635 : ℝ := (9241429 / 40000000)
noncomputable def tm12635 : ℝ := (-((3024641377 / 5000000000)))
noncomputable def ep12635 : ℝ := (51241856193105507 / 100000000000000000000)
noncomputable def em12635 : ℝ := (49950395892343819 / 100000000000000000000)
noncomputable def bp12635 : ℝ := (11129227530580349179 / 25000000000000000000)
noncomputable def bm12635 : ℝ := (45434245227149174569 / 100000000000000000000)

theorem positive12635 :
    Eplus aL (agent12635.root+dsL) scalar12635.worldRadius world12635.frame
      agent12635.frame tp12635 ≤ -ep12635 := by
  apply positive_check (eT := (115575186710649486153 / 100000000000000000000)) (y := (18906944866001665933 / 50000000000000000000)) (u := (145956565855552443123 / 100000000000000000000))
  · norm_num [world12635, agent12635, scalar12635, tp12635, tm12635, ep12635, em12635, dsL]
  · norm_num [world12635, agent12635, scalar12635, tp12635, tm12635, ep12635, em12635, dsL]
  · norm_num [world12635, agent12635, scalar12635, tp12635, tm12635, ep12635, em12635, dsL]
  · norm_num [world12635, agent12635, scalar12635, tp12635, tm12635, ep12635, em12635, dsL]
  · norm_num [world12635, agent12635, scalar12635, tp12635, tm12635, ep12635, em12635, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12635, agent12635, tp12635, tm12635, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12635, agent12635, scalar12635, tp12635, tm12635, ep12635, em12635, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12635, agent12635, tp12635, tm12635, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12635, agent12635, scalar12635, tp12635, tm12635, ep12635, em12635, dsL]

theorem negative12635 :
    Eminus aL (agent12635.root+dsL) scalar12635.worldRadius world12635.frame
      agent12635.frame tm12635 ≤ -em12635 := by
  apply negative_check (lo := (68454118860961800531 / 100000000000000000000)) (hi := (17113529715240450133 / 25000000000000000000))
    (y := (-((35847604920824658711 / 50000000000000000000)))) (u := (48823809212263606741 / 100000000000000000000))
  · norm_num [world12635, agent12635, scalar12635, tp12635, tm12635, ep12635, em12635, dsL]
  · norm_num [world12635, agent12635, scalar12635, tp12635, tm12635, ep12635, em12635, dsL]
  · norm_num [world12635, agent12635, scalar12635, tp12635, tm12635, ep12635, em12635, dsL]
  · norm_num [world12635, agent12635, scalar12635, tp12635, tm12635, ep12635, em12635, dsL]
  · norm_num [world12635, agent12635, scalar12635, tp12635, tm12635, ep12635, em12635, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12635, agent12635, tp12635, tm12635, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12635, agent12635, tp12635, tm12635, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12635, agent12635, scalar12635, tp12635, tm12635, ep12635, em12635, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12635, agent12635, tp12635, tm12635, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12635, agent12635, scalar12635, tp12635, tm12635, ep12635, em12635, dsL]

theorem tails12635 :
    exp (-((12635:ℝ)*ep12635)) ≤ scalar12635.upperTail ∧
    exp (-((12635:ℝ)*em12635)) ≤ scalar12635.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12635:ℝ)) (by norm_num [ep12635]) ?_)
      (show bp12635^8 ≤ scalar12635.upperTail by norm_num [bp12635, scalar12635])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12635, bp12635, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12635:ℝ)) (by norm_num [em12635]) ?_)
      (show bm12635^8 ≤ scalar12635.lowerTail by norm_num [bm12635, scalar12635])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12635, bm12635, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12635 :
    agent12635.root+dsL+scalar12635.worldRadius < √(1/100/aL) ∧
    2*(agent12635.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12635, agent12635, scalar12635, tp12635, tm12635, ep12635, em12635, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12635, agent12635, scalar12635, tp12635, tm12635, ep12635, em12635, dsL]

noncomputable def master12635 : MasterCertificate 12635 world12635 agent12635 :=
  master scalar12635 dsL tp12635 tm12635 ep12635 em12635
    (by norm_num [dsL]) (by norm_num [tp12635]) (by norm_num [tm12635])
    (by norm_num [ep12635]) (by norm_num [em12635])
    positive12635 negative12635 tails12635.1 tails12635.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12635.1 tailGuards12635.2

theorem preserves12635 : master12635.toScalarCertificate = scalar12635 := rfl

noncomputable def tp12636 : ℝ := (1155222359 / 5000000000)
noncomputable def tm12636 : ℝ := (-((1209894147 / 2000000000)))
noncomputable def ep12636 : ℝ := (51244556743522329 / 100000000000000000000)
noncomputable def em12636 : ℝ := (24976358120090777 / 50000000000000000000)
noncomputable def bp12636 : ℝ := (44512160086944680391 / 100000000000000000000)
noncomputable def bm12636 : ℝ := (45429743466741664943 / 100000000000000000000)

theorem positive12636 :
    Eplus aL (agent12636.root+dsL) scalar12636.worldRadius world12636.frame
      agent12636.frame tp12636 ≤ -ep12636 := by
  apply positive_check (eT := (4623017862587134187 / 4000000000000000000)) (y := (9453677897410499491 / 25000000000000000000)) (u := (3648944135391684829 / 2500000000000000000))
  · norm_num [world12636, agent12636, scalar12636, tp12636, tm12636, ep12636, em12636, dsL]
  · norm_num [world12636, agent12636, scalar12636, tp12636, tm12636, ep12636, em12636, dsL]
  · norm_num [world12636, agent12636, scalar12636, tp12636, tm12636, ep12636, em12636, dsL]
  · norm_num [world12636, agent12636, scalar12636, tp12636, tm12636, ep12636, em12636, dsL]
  · norm_num [world12636, agent12636, scalar12636, tp12636, tm12636, ep12636, em12636, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12636, agent12636, tp12636, tm12636, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12636, agent12636, scalar12636, tp12636, tm12636, ep12636, em12636, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12636, agent12636, tp12636, tm12636, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12636, agent12636, scalar12636, tp12636, tm12636, ep12636, em12636, dsL]

theorem negative12636 :
    Eminus aL (agent12636.root+dsL) scalar12636.worldRadius world12636.frame
      agent12636.frame tm12636 ≤ -em12636 := by
  apply negative_check (lo := (34226945942245095923 / 50000000000000000000)) (hi := (68453891884490191847 / 100000000000000000000))
    (y := (-((1433906319419772659 / 2000000000000000000)))) (u := (12205939348976239319 / 25000000000000000000))
  · norm_num [world12636, agent12636, scalar12636, tp12636, tm12636, ep12636, em12636, dsL]
  · norm_num [world12636, agent12636, scalar12636, tp12636, tm12636, ep12636, em12636, dsL]
  · norm_num [world12636, agent12636, scalar12636, tp12636, tm12636, ep12636, em12636, dsL]
  · norm_num [world12636, agent12636, scalar12636, tp12636, tm12636, ep12636, em12636, dsL]
  · norm_num [world12636, agent12636, scalar12636, tp12636, tm12636, ep12636, em12636, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12636, agent12636, tp12636, tm12636, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12636, agent12636, tp12636, tm12636, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12636, agent12636, scalar12636, tp12636, tm12636, ep12636, em12636, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12636, agent12636, tp12636, tm12636, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12636, agent12636, scalar12636, tp12636, tm12636, ep12636, em12636, dsL]

theorem tails12636 :
    exp (-((12636:ℝ)*ep12636)) ≤ scalar12636.upperTail ∧
    exp (-((12636:ℝ)*em12636)) ≤ scalar12636.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12636:ℝ)) (by norm_num [ep12636]) ?_)
      (show bp12636^8 ≤ scalar12636.upperTail by norm_num [bp12636, scalar12636])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12636, bp12636, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12636:ℝ)) (by norm_num [em12636]) ?_)
      (show bm12636^8 ≤ scalar12636.lowerTail by norm_num [bm12636, scalar12636])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12636, bm12636, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12636 :
    agent12636.root+dsL+scalar12636.worldRadius < √(1/100/aL) ∧
    2*(agent12636.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12636, agent12636, scalar12636, tp12636, tm12636, ep12636, em12636, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12636, agent12636, scalar12636, tp12636, tm12636, ep12636, em12636, dsL]

noncomputable def master12636 : MasterCertificate 12636 world12636 agent12636 :=
  master scalar12636 dsL tp12636 tm12636 ep12636 em12636
    (by norm_num [dsL]) (by norm_num [tp12636]) (by norm_num [tm12636])
    (by norm_num [ep12636]) (by norm_num [em12636])
    positive12636 negative12636 tails12636.1 tails12636.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12636.1 tailGuards12636.2

theorem preserves12636 : master12636.toScalarCertificate = scalar12636 := rfl

noncomputable def tp12637 : ℝ := (2310532097 / 10000000000)
noncomputable def tm12637 : ℝ := (-((3024829221 / 5000000000)))
noncomputable def ep12637 : ℝ := (6405906918582973 / 12500000000000000000)
noncomputable def em12637 : ℝ := (4995503483649113 / 10000000000000000000)
noncomputable def bp12637 : ℝ := (44507411625545340943 / 100000000000000000000)
noncomputable def bm12637 : ℝ := (709769424151288543 / 1562500000000000000)

theorem positive12637 :
    Eplus aL (agent12637.root+dsL) scalar12637.worldRadius world12637.frame
      agent12637.frame tp12637 ≤ -ep12637 := by
  apply positive_check (eT := (14446963225862380061 / 12500000000000000000)) (y := (37815532108617163567 / 100000000000000000000)) (u := (7297948151587084163 / 5000000000000000000))
  · norm_num [world12637, agent12637, scalar12637, tp12637, tm12637, ep12637, em12637, dsL]
  · norm_num [world12637, agent12637, scalar12637, tp12637, tm12637, ep12637, em12637, dsL]
  · norm_num [world12637, agent12637, scalar12637, tp12637, tm12637, ep12637, em12637, dsL]
  · norm_num [world12637, agent12637, scalar12637, tp12637, tm12637, ep12637, em12637, dsL]
  · norm_num [world12637, agent12637, scalar12637, tp12637, tm12637, ep12637, em12637, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12637, agent12637, tp12637, tm12637, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12637, agent12637, scalar12637, tp12637, tm12637, ep12637, em12637, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12637, agent12637, tp12637, tm12637, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12637, agent12637, scalar12637, tp12637, tm12637, ep12637, em12637, dsL]

theorem negative12637 :
    Eminus aL (agent12637.root+dsL) scalar12637.worldRadius world12637.frame
      agent12637.frame tm12637 ≤ -em12637 := by
  apply negative_check (lo := (34226833013154298963 / 50000000000000000000)) (hi := (68453666026308597927 / 100000000000000000000))
    (y := (-((71695419595388971947 / 100000000000000000000)))) (u := (48823706802605346309 / 100000000000000000000))
  · norm_num [world12637, agent12637, scalar12637, tp12637, tm12637, ep12637, em12637, dsL]
  · norm_num [world12637, agent12637, scalar12637, tp12637, tm12637, ep12637, em12637, dsL]
  · norm_num [world12637, agent12637, scalar12637, tp12637, tm12637, ep12637, em12637, dsL]
  · norm_num [world12637, agent12637, scalar12637, tp12637, tm12637, ep12637, em12637, dsL]
  · norm_num [world12637, agent12637, scalar12637, tp12637, tm12637, ep12637, em12637, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12637, agent12637, tp12637, tm12637, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12637, agent12637, tp12637, tm12637, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12637, agent12637, scalar12637, tp12637, tm12637, ep12637, em12637, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12637, agent12637, tp12637, tm12637, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12637, agent12637, scalar12637, tp12637, tm12637, ep12637, em12637, dsL]

theorem tails12637 :
    exp (-((12637:ℝ)*ep12637)) ≤ scalar12637.upperTail ∧
    exp (-((12637:ℝ)*em12637)) ≤ scalar12637.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12637:ℝ)) (by norm_num [ep12637]) ?_)
      (show bp12637^8 ≤ scalar12637.upperTail by norm_num [bp12637, scalar12637])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12637, bp12637, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12637:ℝ)) (by norm_num [em12637]) ?_)
      (show bm12637^8 ≤ scalar12637.lowerTail by norm_num [bm12637, scalar12637])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12637, bm12637, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12637 :
    agent12637.root+dsL+scalar12637.worldRadius < √(1/100/aL) ∧
    2*(agent12637.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12637, agent12637, scalar12637, tp12637, tm12637, ep12637, em12637, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12637, agent12637, scalar12637, tp12637, tm12637, ep12637, em12637, dsL]

noncomputable def master12637 : MasterCertificate 12637 world12637 agent12637 :=
  master scalar12637 dsL tp12637 tm12637 ep12637 em12637
    (by norm_num [dsL]) (by norm_num [tp12637]) (by norm_num [tm12637])
    (by norm_num [ep12637]) (by norm_num [em12637])
    positive12637 negative12637 tails12637.1 tails12637.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12637.1 tailGuards12637.2

theorem preserves12637 : master12637.toScalarCertificate = scalar12637 := rfl

noncomputable def tp12638 : ℝ := (1155309741 / 5000000000)
noncomputable def tm12638 : ℝ := (-((3024923039 / 5000000000)))
noncomputable def ep12638 : ℝ := (25624976578412371 / 50000000000000000000)
noncomputable def em12638 : ℝ := (49957352647095749 / 100000000000000000000)
noncomputable def bp12638 : ℝ := (44502663930765707763 / 100000000000000000000)
noncomputable def bm12638 : ℝ := (5677592946364918157 / 12500000000000000000)

theorem positive12638 :
    Eplus aL (agent12638.root+dsL) scalar12638.worldRadius world12638.frame
      agent12638.frame tp12638 ≤ -ep12638 := by
  apply positive_check (eT := (115575965125144792473 / 100000000000000000000)) (y := (9454088329504658343 / 25000000000000000000)) (u := (18245020208173753391 / 12500000000000000000))
  · norm_num [world12638, agent12638, scalar12638, tp12638, tm12638, ep12638, em12638, dsL]
  · norm_num [world12638, agent12638, scalar12638, tp12638, tm12638, ep12638, em12638, dsL]
  · norm_num [world12638, agent12638, scalar12638, tp12638, tm12638, ep12638, em12638, dsL]
  · norm_num [world12638, agent12638, scalar12638, tp12638, tm12638, ep12638, em12638, dsL]
  · norm_num [world12638, agent12638, scalar12638, tp12638, tm12638, ep12638, em12638, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12638, agent12638, tp12638, tm12638, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12638, agent12638, scalar12638, tp12638, tm12638, ep12638, em12638, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12638, agent12638, tp12638, tm12638, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12638, agent12638, scalar12638, tp12638, tm12638, ep12638, em12638, dsL]

theorem negative12638 :
    Eminus aL (agent12638.root+dsL) scalar12638.worldRadius world12638.frame
      agent12638.frame tm12638 ≤ -em12638 := by
  apply negative_check (lo := (68453440415870244891 / 100000000000000000000)) (hi := (17113360103967561223 / 25000000000000000000))
    (y := (-((8961940477364907187 / 12500000000000000000)))) (u := (24411827958420508921 / 50000000000000000000))
  · norm_num [world12638, agent12638, scalar12638, tp12638, tm12638, ep12638, em12638, dsL]
  · norm_num [world12638, agent12638, scalar12638, tp12638, tm12638, ep12638, em12638, dsL]
  · norm_num [world12638, agent12638, scalar12638, tp12638, tm12638, ep12638, em12638, dsL]
  · norm_num [world12638, agent12638, scalar12638, tp12638, tm12638, ep12638, em12638, dsL]
  · norm_num [world12638, agent12638, scalar12638, tp12638, tm12638, ep12638, em12638, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12638, agent12638, tp12638, tm12638, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12638, agent12638, tp12638, tm12638, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12638, agent12638, scalar12638, tp12638, tm12638, ep12638, em12638, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12638, agent12638, tp12638, tm12638, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12638, agent12638, scalar12638, tp12638, tm12638, ep12638, em12638, dsL]

theorem tails12638 :
    exp (-((12638:ℝ)*ep12638)) ≤ scalar12638.upperTail ∧
    exp (-((12638:ℝ)*em12638)) ≤ scalar12638.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12638:ℝ)) (by norm_num [ep12638]) ?_)
      (show bp12638^8 ≤ scalar12638.upperTail by norm_num [bp12638, scalar12638])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12638, bp12638, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12638:ℝ)) (by norm_num [em12638]) ?_)
      (show bm12638^8 ≤ scalar12638.lowerTail by norm_num [bm12638, scalar12638])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12638, bm12638, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12638 :
    agent12638.root+dsL+scalar12638.worldRadius < √(1/100/aL) ∧
    2*(agent12638.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12638, agent12638, scalar12638, tp12638, tm12638, ep12638, em12638, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12638, agent12638, scalar12638, tp12638, tm12638, ep12638, em12638, dsL]

noncomputable def master12638 : MasterCertificate 12638 world12638 agent12638 :=
  master scalar12638 dsL tp12638 tm12638 ep12638 em12638
    (by norm_num [dsL]) (by norm_num [tp12638]) (by norm_num [tm12638])
    (by norm_num [ep12638]) (by norm_num [em12638])
    positive12638 negative12638 tails12638.1 tails12638.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12638.1 tailGuards12638.2

theorem preserves12638 : master12638.toScalarCertificate = scalar12638 := rfl

noncomputable def tp12639 : ℝ := (462141367 / 2000000000)
noncomputable def tm12639 : ℝ := (-((1512508431 / 2500000000)))
noncomputable def ep12639 : ℝ := (10250529961262993 / 20000000000000000000)
noncomputable def em12639 : ℝ := (624495867639751 / 1250000000000000000)
noncomputable def bp12639 : ℝ := (11124479314218473271 / 25000000000000000000)
noncomputable def bm12639 : ℝ := (45416244929592847751 / 100000000000000000000)

theorem positive12639 :
    Eplus aL (agent12639.root+dsL) scalar12639.worldRadius world12639.frame
      agent12639.frame tp12639 ≤ -ep12639 := by
  apply positive_check (eT := (115576224244331987967 / 100000000000000000000)) (y := (37817174142522346631 / 100000000000000000000)) (u := (145961359747079703451 / 100000000000000000000))
  · norm_num [world12639, agent12639, scalar12639, tp12639, tm12639, ep12639, em12639, dsL]
  · norm_num [world12639, agent12639, scalar12639, tp12639, tm12639, ep12639, em12639, dsL]
  · norm_num [world12639, agent12639, scalar12639, tp12639, tm12639, ep12639, em12639, dsL]
  · norm_num [world12639, agent12639, scalar12639, tp12639, tm12639, ep12639, em12639, dsL]
  · norm_num [world12639, agent12639, scalar12639, tp12639, tm12639, ep12639, em12639, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12639, agent12639, tp12639, tm12639, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12639, agent12639, scalar12639, tp12639, tm12639, ep12639, em12639, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12639, agent12639, tp12639, tm12639, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12639, agent12639, scalar12639, tp12639, tm12639, ep12639, em12639, dsL]

theorem negative12639 :
    Eminus aL (agent12639.root+dsL) scalar12639.worldRadius world12639.frame
      agent12639.frame tm12639 ≤ -em12639 := by
  apply negative_check (lo := (34226607352849182403 / 50000000000000000000)) (hi := (68453214705698364807 / 100000000000000000000))
    (y := (-((14339125687284743801 / 20000000000000000000)))) (u := (3051475302423583067 / 6250000000000000000))
  · norm_num [world12639, agent12639, scalar12639, tp12639, tm12639, ep12639, em12639, dsL]
  · norm_num [world12639, agent12639, scalar12639, tp12639, tm12639, ep12639, em12639, dsL]
  · norm_num [world12639, agent12639, scalar12639, tp12639, tm12639, ep12639, em12639, dsL]
  · norm_num [world12639, agent12639, scalar12639, tp12639, tm12639, ep12639, em12639, dsL]
  · norm_num [world12639, agent12639, scalar12639, tp12639, tm12639, ep12639, em12639, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12639, agent12639, tp12639, tm12639, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12639, agent12639, tp12639, tm12639, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12639, agent12639, scalar12639, tp12639, tm12639, ep12639, em12639, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12639, agent12639, tp12639, tm12639, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12639, agent12639, scalar12639, tp12639, tm12639, ep12639, em12639, dsL]

theorem tails12639 :
    exp (-((12639:ℝ)*ep12639)) ≤ scalar12639.upperTail ∧
    exp (-((12639:ℝ)*em12639)) ≤ scalar12639.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12639:ℝ)) (by norm_num [ep12639]) ?_)
      (show bp12639^8 ≤ scalar12639.upperTail by norm_num [bp12639, scalar12639])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12639, bp12639, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12639:ℝ)) (by norm_num [em12639]) ?_)
      (show bm12639^8 ≤ scalar12639.lowerTail by norm_num [bm12639, scalar12639])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12639, bm12639, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12639 :
    agent12639.root+dsL+scalar12639.worldRadius < √(1/100/aL) ∧
    2*(agent12639.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12639, agent12639, scalar12639, tp12639, tm12639, ep12639, em12639, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12639, agent12639, scalar12639, tp12639, tm12639, ep12639, em12639, dsL]

noncomputable def master12639 : MasterCertificate 12639 world12639 agent12639 :=
  master scalar12639 dsL tp12639 tm12639 ep12639 em12639
    (by norm_num [dsL]) (by norm_num [tp12639]) (by norm_num [tm12639])
    (by norm_num [ep12639]) (by norm_num [em12639])
    positive12639 negative12639 tails12639.1 tails12639.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12639.1 tailGuards12639.2

theorem preserves12639 : master12639.toScalarCertificate = scalar12639 := rfl

noncomputable def tp12640 : ℝ := (115543453 / 500000000)
noncomputable def tm12640 : ℝ := (-((6050447557 / 10000000000)))
noncomputable def ep12640 : ℝ := (51256779337373767 / 100000000000000000000)
noncomputable def em12640 : ℝ := (4996354670303947 / 10000000000000000000)
noncomputable def bp12640 : ℝ := (44492163496289812959 / 100000000000000000000)
noncomputable def bm12640 : ℝ := (45410626797202966121 / 100000000000000000000)

theorem positive12640 :
    Eplus aL (agent12640.root+dsL) scalar12640.worldRadius world12640.frame
      agent12640.frame tp12640 ≤ -ep12640 := by
  apply positive_check (eT := (115577025502095658877 / 100000000000000000000)) (y := (37817267655733616977 / 100000000000000000000)) (u := (145961496240298236393 / 100000000000000000000))
  · norm_num [world12640, agent12640, scalar12640, tp12640, tm12640, ep12640, em12640, dsL]
  · norm_num [world12640, agent12640, scalar12640, tp12640, tm12640, ep12640, em12640, dsL]
  · norm_num [world12640, agent12640, scalar12640, tp12640, tm12640, ep12640, em12640, dsL]
  · norm_num [world12640, agent12640, scalar12640, tp12640, tm12640, ep12640, em12640, dsL]
  · norm_num [world12640, agent12640, scalar12640, tp12640, tm12640, ep12640, em12640, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12640, agent12640, tp12640, tm12640, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12640, agent12640, scalar12640, tp12640, tm12640, ep12640, em12640, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12640, agent12640, tp12640, tm12640, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12640, agent12640, scalar12640, tp12640, tm12640, ep12640, em12640, dsL]

theorem negative12640 :
    Eminus aL (agent12640.root+dsL) scalar12640.worldRadius world12640.frame
      agent12640.frame tm12640 ≤ -em12640 := by
  apply negative_check (lo := (1369040379690376893 / 2000000000000000000)) (hi := (68452018984518844651 / 100000000000000000000))
    (y := (-((35846908522711862237 / 50000000000000000000)))) (u := (6103061154146393453 / 12500000000000000000))
  · norm_num [world12640, agent12640, scalar12640, tp12640, tm12640, ep12640, em12640, dsL]
  · norm_num [world12640, agent12640, scalar12640, tp12640, tm12640, ep12640, em12640, dsL]
  · norm_num [world12640, agent12640, scalar12640, tp12640, tm12640, ep12640, em12640, dsL]
  · norm_num [world12640, agent12640, scalar12640, tp12640, tm12640, ep12640, em12640, dsL]
  · norm_num [world12640, agent12640, scalar12640, tp12640, tm12640, ep12640, em12640, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12640, agent12640, tp12640, tm12640, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12640, agent12640, tp12640, tm12640, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12640, agent12640, scalar12640, tp12640, tm12640, ep12640, em12640, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12640, agent12640, tp12640, tm12640, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12640, agent12640, scalar12640, tp12640, tm12640, ep12640, em12640, dsL]

theorem tails12640 :
    exp (-((12640:ℝ)*ep12640)) ≤ scalar12640.upperTail ∧
    exp (-((12640:ℝ)*em12640)) ≤ scalar12640.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12640:ℝ)) (by norm_num [ep12640]) ?_)
      (show bp12640^8 ≤ scalar12640.upperTail by norm_num [bp12640, scalar12640])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12640, bp12640, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12640:ℝ)) (by norm_num [em12640]) ?_)
      (show bm12640^8 ≤ scalar12640.lowerTail by norm_num [bm12640, scalar12640])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12640, bm12640, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12640 :
    agent12640.root+dsL+scalar12640.worldRadius < √(1/100/aL) ∧
    2*(agent12640.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12640, agent12640, scalar12640, tp12640, tm12640, ep12640, em12640, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12640, agent12640, scalar12640, tp12640, tm12640, ep12640, em12640, dsL]

noncomputable def master12640 : MasterCertificate 12640 world12640 agent12640 :=
  master scalar12640 dsL tp12640 tm12640 ep12640 em12640
    (by norm_num [dsL]) (by norm_num [tp12640]) (by norm_num [tm12640])
    (by norm_num [ep12640]) (by norm_num [em12640])
    positive12640 negative12640 tails12640.1 tails12640.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12640.1 tailGuards12640.2

theorem preserves12640 : master12640.toScalarCertificate = scalar12640 := rfl

noncomputable def tp12641 : ℝ := (462191263 / 2000000000)
noncomputable def tm12641 : ℝ := (-((1512658773 / 2500000000)))
noncomputable def ep12641 : ℝ := (2562973660321439 / 5000000000000000000)
noncomputable def em12641 : ℝ := (24982930441249057 / 50000000000000000000)
noncomputable def bp12641 : ℝ := (44487419217388526649 / 100000000000000000000)
noncomputable def bm12641 : ℝ := (5675766299716519343 / 12500000000000000000)

theorem positive12641 :
    Eplus aL (agent12641.root+dsL) scalar12641.worldRadius world12641.frame
      agent12641.frame tp12641 ≤ -ep12641 := by
  apply positive_check (eT := (57788641983019537331 / 50000000000000000000)) (y := (18909043816725483037 / 50000000000000000000)) (u := (145962693096950288401 / 100000000000000000000))
  · norm_num [world12641, agent12641, scalar12641, tp12641, tm12641, ep12641, em12641, dsL]
  · norm_num [world12641, agent12641, scalar12641, tp12641, tm12641, ep12641, em12641, dsL]
  · norm_num [world12641, agent12641, scalar12641, tp12641, tm12641, ep12641, em12641, dsL]
  · norm_num [world12641, agent12641, scalar12641, tp12641, tm12641, ep12641, em12641, dsL]
  · norm_num [world12641, agent12641, scalar12641, tp12641, tm12641, ep12641, em12641, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12641, agent12641, tp12641, tm12641, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12641, agent12641, scalar12641, tp12641, tm12641, ep12641, em12641, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12641, agent12641, tp12641, tm12641, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12641, agent12641, scalar12641, tp12641, tm12641, ep12641, em12641, dsL]

theorem negative12641 :
    Eminus aL (agent12641.root+dsL) scalar12641.worldRadius world12641.frame
      agent12641.frame tm12641 ≤ -em12641 := by
  apply negative_check (lo := (17112948415414745569 / 25000000000000000000)) (hi := (68451793661658982277 / 100000000000000000000))
    (y := (-((8961740276002183889 / 12500000000000000000)))) (u := (48824437888098884383 / 100000000000000000000))
  · norm_num [world12641, agent12641, scalar12641, tp12641, tm12641, ep12641, em12641, dsL]
  · norm_num [world12641, agent12641, scalar12641, tp12641, tm12641, ep12641, em12641, dsL]
  · norm_num [world12641, agent12641, scalar12641, tp12641, tm12641, ep12641, em12641, dsL]
  · norm_num [world12641, agent12641, scalar12641, tp12641, tm12641, ep12641, em12641, dsL]
  · norm_num [world12641, agent12641, scalar12641, tp12641, tm12641, ep12641, em12641, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12641, agent12641, tp12641, tm12641, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12641, agent12641, tp12641, tm12641, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12641, agent12641, scalar12641, tp12641, tm12641, ep12641, em12641, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12641, agent12641, tp12641, tm12641, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12641, agent12641, scalar12641, tp12641, tm12641, ep12641, em12641, dsL]

theorem tails12641 :
    exp (-((12641:ℝ)*ep12641)) ≤ scalar12641.upperTail ∧
    exp (-((12641:ℝ)*em12641)) ≤ scalar12641.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12641:ℝ)) (by norm_num [ep12641]) ?_)
      (show bp12641^8 ≤ scalar12641.upperTail by norm_num [bp12641, scalar12641])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12641, bp12641, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12641:ℝ)) (by norm_num [em12641]) ?_)
      (show bm12641^8 ≤ scalar12641.lowerTail by norm_num [bm12641, scalar12641])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12641, bm12641, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12641 :
    agent12641.root+dsL+scalar12641.worldRadius < √(1/100/aL) ∧
    2*(agent12641.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12641, agent12641, scalar12641, tp12641, tm12641, ep12641, em12641, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12641, agent12641, scalar12641, tp12641, tm12641, ep12641, em12641, dsL]

noncomputable def master12641 : MasterCertificate 12641 world12641 agent12641 :=
  master scalar12641 dsL tp12641 tm12641 ep12641 em12641
    (by norm_num [dsL]) (by norm_num [tp12641]) (by norm_num [tm12641])
    (by norm_num [ep12641]) (by norm_num [em12641])
    positive12641 negative12641 tails12641.1 tails12641.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12641.1 tailGuards12641.2

theorem preserves12641 : master12641.toScalarCertificate = scalar12641 := rfl

noncomputable def tp12642 : ℝ := (1155521753 / 5000000000)
noncomputable def tm12642 : ℝ := (-((6050822191 / 10000000000)))
noncomputable def ep12642 : ℝ := (25631082654705871 / 50000000000000000000)
noncomputable def em12642 : ℝ := (4996817343626489 / 10000000000000000000)
noncomputable def bp12642 : ℝ := (44482676386240165191 / 100000000000000000000)
noncomputable def bm12642 : ℝ := (1816065413887115109 / 4000000000000000000)

theorem positive12642 :
    Eplus aL (agent12642.root+dsL) scalar12642.worldRadius world12642.frame
      agent12642.frame tp12642 ≤ -ep12642 := by
  apply positive_check (eT := (28894385499814788697 / 25000000000000000000)) (y := (18909453431958572149 / 50000000000000000000)) (u := (145963888872699465771 / 100000000000000000000))
  · norm_num [world12642, agent12642, scalar12642, tp12642, tm12642, ep12642, em12642, dsL]
  · norm_num [world12642, agent12642, scalar12642, tp12642, tm12642, ep12642, em12642, dsL]
  · norm_num [world12642, agent12642, scalar12642, tp12642, tm12642, ep12642, em12642, dsL]
  · norm_num [world12642, agent12642, scalar12642, tp12642, tm12642, ep12642, em12642, dsL]
  · norm_num [world12642, agent12642, scalar12642, tp12642, tm12642, ep12642, em12642, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12642, agent12642, tp12642, tm12642, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12642, agent12642, scalar12642, tp12642, tm12642, ep12642, em12642, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12642, agent12642, tp12642, tm12642, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12642, agent12642, scalar12642, tp12642, tm12642, ep12642, em12642, dsL]

theorem negative12642 :
    Eminus aL (agent12642.root+dsL) scalar12642.worldRadius world12642.frame
      agent12642.frame tm12642 ≤ -em12642 := by
  apply negative_check (lo := (68451570151566428427 / 100000000000000000000)) (hi := (17112892537891607107 / 25000000000000000000))
    (y := (-((35847011788370985317 / 50000000000000000000)))) (u := (48824388395414038211 / 100000000000000000000))
  · norm_num [world12642, agent12642, scalar12642, tp12642, tm12642, ep12642, em12642, dsL]
  · norm_num [world12642, agent12642, scalar12642, tp12642, tm12642, ep12642, em12642, dsL]
  · norm_num [world12642, agent12642, scalar12642, tp12642, tm12642, ep12642, em12642, dsL]
  · norm_num [world12642, agent12642, scalar12642, tp12642, tm12642, ep12642, em12642, dsL]
  · norm_num [world12642, agent12642, scalar12642, tp12642, tm12642, ep12642, em12642, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12642, agent12642, tp12642, tm12642, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12642, agent12642, tp12642, tm12642, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12642, agent12642, scalar12642, tp12642, tm12642, ep12642, em12642, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12642, agent12642, tp12642, tm12642, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12642, agent12642, scalar12642, tp12642, tm12642, ep12642, em12642, dsL]

theorem tails12642 :
    exp (-((12642:ℝ)*ep12642)) ≤ scalar12642.upperTail ∧
    exp (-((12642:ℝ)*em12642)) ≤ scalar12642.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12642:ℝ)) (by norm_num [ep12642]) ?_)
      (show bp12642^8 ≤ scalar12642.upperTail by norm_num [bp12642, scalar12642])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12642, bp12642, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12642:ℝ)) (by norm_num [em12642]) ?_)
      (show bm12642^8 ≤ scalar12642.lowerTail by norm_num [bm12642, scalar12642])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12642, bm12642, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12642 :
    agent12642.root+dsL+scalar12642.worldRadius < √(1/100/aL) ∧
    2*(agent12642.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12642, agent12642, scalar12642, tp12642, tm12642, ep12642, em12642, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12642, agent12642, scalar12642, tp12642, tm12642, ep12642, em12642, dsL]

noncomputable def master12642 : MasterCertificate 12642 world12642 agent12642 :=
  master scalar12642 dsL tp12642 tm12642 ep12642 em12642
    (by norm_num [dsL]) (by norm_num [tp12642]) (by norm_num [tm12642])
    (by norm_num [ep12642]) (by norm_num [em12642])
    positive12642 negative12642 tails12642.1 tails12642.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12642.1 tailGuards12642.2

theorem preserves12642 : master12642.toScalarCertificate = scalar12642 := rfl

noncomputable def tp12643 : ℝ := (2311130907 / 10000000000)
noncomputable def tm12643 : ℝ := (-((6051010091 / 10000000000)))
noncomputable def ep12643 : ℝ := (10252972010909793 / 20000000000000000000)
noncomputable def em12643 : ℝ := (24985244572339827 / 50000000000000000000)
noncomputable def bp12643 : ℝ := (1389935372005058459 / 3125000000000000000)
noncomputable def bm12643 : ℝ := (45397138215873250689 / 100000000000000000000)

theorem positive12643 :
    Eplus aL (agent12643.root+dsL) scalar12643.worldRadius world12643.frame
      agent12643.frame tp12643 ≤ -ep12643 := by
  apply positive_check (eT := (57788900792751130357 / 50000000000000000000)) (y := (3781972419258778023 / 10000000000000000000)) (u := (18245635235285924447 / 12500000000000000000))
  · norm_num [world12643, agent12643, scalar12643, tp12643, tm12643, ep12643, em12643, dsL]
  · norm_num [world12643, agent12643, scalar12643, tp12643, tm12643, ep12643, em12643, dsL]
  · norm_num [world12643, agent12643, scalar12643, tp12643, tm12643, ep12643, em12643, dsL]
  · norm_num [world12643, agent12643, scalar12643, tp12643, tm12643, ep12643, em12643, dsL]
  · norm_num [world12643, agent12643, scalar12643, tp12643, tm12643, ep12643, em12643, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12643, agent12643, tp12643, tm12643, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12643, agent12643, scalar12643, tp12643, tm12643, ep12643, em12643, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12643, agent12643, tp12643, tm12643, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12643, agent12643, scalar12643, tp12643, tm12643, ep12643, em12643, dsL]

theorem negative12643 :
    Eminus aL (agent12643.root+dsL) scalar12643.worldRadius world12643.frame
      agent12643.frame tm12643 ≤ -em12643 := by
  apply negative_check (lo := (34225671575004563269 / 50000000000000000000)) (hi := (68451343150009126539 / 100000000000000000000))
    (y := (-((35847060721888594497 / 50000000000000000000)))) (u := (48824340612456034009 / 100000000000000000000))
  · norm_num [world12643, agent12643, scalar12643, tp12643, tm12643, ep12643, em12643, dsL]
  · norm_num [world12643, agent12643, scalar12643, tp12643, tm12643, ep12643, em12643, dsL]
  · norm_num [world12643, agent12643, scalar12643, tp12643, tm12643, ep12643, em12643, dsL]
  · norm_num [world12643, agent12643, scalar12643, tp12643, tm12643, ep12643, em12643, dsL]
  · norm_num [world12643, agent12643, scalar12643, tp12643, tm12643, ep12643, em12643, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12643, agent12643, tp12643, tm12643, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12643, agent12643, tp12643, tm12643, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12643, agent12643, scalar12643, tp12643, tm12643, ep12643, em12643, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12643, agent12643, tp12643, tm12643, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12643, agent12643, scalar12643, tp12643, tm12643, ep12643, em12643, dsL]

theorem tails12643 :
    exp (-((12643:ℝ)*ep12643)) ≤ scalar12643.upperTail ∧
    exp (-((12643:ℝ)*em12643)) ≤ scalar12643.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12643:ℝ)) (by norm_num [ep12643]) ?_)
      (show bp12643^8 ≤ scalar12643.upperTail by norm_num [bp12643, scalar12643])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12643, bp12643, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12643:ℝ)) (by norm_num [em12643]) ?_)
      (show bm12643^8 ≤ scalar12643.lowerTail by norm_num [bm12643, scalar12643])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12643, bm12643, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12643 :
    agent12643.root+dsL+scalar12643.worldRadius < √(1/100/aL) ∧
    2*(agent12643.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12643, agent12643, scalar12643, tp12643, tm12643, ep12643, em12643, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12643, agent12643, scalar12643, tp12643, tm12643, ep12643, em12643, dsL]

noncomputable def master12643 : MasterCertificate 12643 world12643 agent12643 :=
  master scalar12643 dsL tp12643 tm12643 ep12643 em12643
    (by norm_num [dsL]) (by norm_num [tp12643]) (by norm_num [tm12643])
    (by norm_num [ep12643]) (by norm_num [em12643])
    positive12643 negative12643 tails12643.1 tails12643.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12643.1 tailGuards12643.2

theorem preserves12643 : master12643.toScalarCertificate = scalar12643 := rfl

noncomputable def tp12644 : ℝ := (2311218339 / 10000000000)
noncomputable def tm12644 : ℝ := (-((3025598999 / 5000000000)))
noncomputable def ep12644 : ℝ := (25633777664275601 / 50000000000000000000)
noncomputable def em12644 : ℝ := (9994561113174279 / 20000000000000000000)
noncomputable def bp12644 : ℝ := (44473187256777436921 / 100000000000000000000)
noncomputable def bm12644 : ℝ := (1418520023620654193 / 3125000000000000000)

theorem positive12644 :
    Eplus aL (agent12644.root+dsL) scalar12644.worldRadius world12644.frame
      agent12644.frame tp12644 ≤ -ep12644 := by
  apply positive_check (eT := (115578061428746755467 / 100000000000000000000)) (y := (236378377003544777 / 625000000000000000)) (u := (145966273149021891773 / 100000000000000000000))
  · norm_num [world12644, agent12644, scalar12644, tp12644, tm12644, ep12644, em12644, dsL]
  · norm_num [world12644, agent12644, scalar12644, tp12644, tm12644, ep12644, em12644, dsL]
  · norm_num [world12644, agent12644, scalar12644, tp12644, tm12644, ep12644, em12644, dsL]
  · norm_num [world12644, agent12644, scalar12644, tp12644, tm12644, ep12644, em12644, dsL]
  · norm_num [world12644, agent12644, scalar12644, tp12644, tm12644, ep12644, em12644, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12644, agent12644, tp12644, tm12644, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12644, agent12644, scalar12644, tp12644, tm12644, ep12644, em12644, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12644, agent12644, tp12644, tm12644, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12644, agent12644, scalar12644, tp12644, tm12644, ep12644, em12644, dsL]

theorem negative12644 :
    Eminus aL (agent12644.root+dsL) scalar12644.worldRadius world12644.frame
      agent12644.frame tm12644 ≤ -em12644 := by
  apply negative_check (lo := (68451116061768040699 / 100000000000000000000)) (hi := (684511160617680407 / 1000000000000000000))
    (y := (-((35847107905264721499 / 50000000000000000000)))) (u := (48824294538533227837 / 100000000000000000000))
  · norm_num [world12644, agent12644, scalar12644, tp12644, tm12644, ep12644, em12644, dsL]
  · norm_num [world12644, agent12644, scalar12644, tp12644, tm12644, ep12644, em12644, dsL]
  · norm_num [world12644, agent12644, scalar12644, tp12644, tm12644, ep12644, em12644, dsL]
  · norm_num [world12644, agent12644, scalar12644, tp12644, tm12644, ep12644, em12644, dsL]
  · norm_num [world12644, agent12644, scalar12644, tp12644, tm12644, ep12644, em12644, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12644, agent12644, tp12644, tm12644, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12644, agent12644, tp12644, tm12644, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12644, agent12644, scalar12644, tp12644, tm12644, ep12644, em12644, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12644, agent12644, tp12644, tm12644, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12644, agent12644, scalar12644, tp12644, tm12644, ep12644, em12644, dsL]

theorem tails12644 :
    exp (-((12644:ℝ)*ep12644)) ≤ scalar12644.upperTail ∧
    exp (-((12644:ℝ)*em12644)) ≤ scalar12644.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12644:ℝ)) (by norm_num [ep12644]) ?_)
      (show bp12644^8 ≤ scalar12644.upperTail by norm_num [bp12644, scalar12644])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12644, bp12644, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12644:ℝ)) (by norm_num [em12644]) ?_)
      (show bm12644^8 ≤ scalar12644.lowerTail by norm_num [bm12644, scalar12644])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12644, bm12644, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12644 :
    agent12644.root+dsL+scalar12644.worldRadius < √(1/100/aL) ∧
    2*(agent12644.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12644, agent12644, scalar12644, tp12644, tm12644, ep12644, em12644, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12644, agent12644, scalar12644, tp12644, tm12644, ep12644, em12644, dsL]

noncomputable def master12644 : MasterCertificate 12644 world12644 agent12644 :=
  master scalar12644 dsL tp12644 tm12644 ep12644 em12644
    (by norm_num [dsL]) (by norm_num [tp12644]) (by norm_num [tm12644])
    (by norm_num [ep12644]) (by norm_num [em12644])
    positive12644 negative12644 tails12644.1 tails12644.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12644.1 tailGuards12644.2

theorem preserves12644 : master12644.toScalarCertificate = scalar12644 := rfl

noncomputable def tp12645 : ℝ := (2311305691 / 10000000000)
noncomputable def tm12645 : ℝ := (-((6051385917 / 10000000000)))
noncomputable def ep12645 : ℝ := (10254049739087491 / 20000000000000000000)
noncomputable def em12645 : ℝ := (24987560107013533 / 50000000000000000000)
noncomputable def bp12645 : ℝ := (44468444156360241171 / 100000000000000000000)
noncomputable def bm12645 : ℝ := (22694072375284246367 / 50000000000000000000)

theorem positive12645 :
    Eplus aL (agent12645.root+dsL) scalar12645.worldRadius world12645.frame
      agent12645.frame tp12645 ≤ -ep12645 := by
  apply positive_check (eT := (1155783207253497339 / 1000000000000000000)) (y := (37821355570910162641 / 100000000000000000000)) (u := (36491865786103778803 / 25000000000000000000))
  · norm_num [world12645, agent12645, scalar12645, tp12645, tm12645, ep12645, em12645, dsL]
  · norm_num [world12645, agent12645, scalar12645, tp12645, tm12645, ep12645, em12645, dsL]
  · norm_num [world12645, agent12645, scalar12645, tp12645, tm12645, ep12645, em12645, dsL]
  · norm_num [world12645, agent12645, scalar12645, tp12645, tm12645, ep12645, em12645, dsL]
  · norm_num [world12645, agent12645, scalar12645, tp12645, tm12645, ep12645, em12645, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12645, agent12645, tp12645, tm12645, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12645, agent12645, scalar12645, tp12645, tm12645, ep12645, em12645, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12645, agent12645, tp12645, tm12645, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12645, agent12645, scalar12645, tp12645, tm12645, ep12645, em12645, dsL]

theorem negative12645 :
    Eminus aL (agent12645.root+dsL) scalar12645.worldRadius world12645.frame
      agent12645.frame tm12645 ≤ -em12645 := by
  apply negative_check (lo := (3422544443272012259 / 5000000000000000000)) (hi := (68450888865440245181 / 100000000000000000000))
    (y := (-((14338862207063082507 / 20000000000000000000)))) (u := (12206062011431347181 / 25000000000000000000))
  · norm_num [world12645, agent12645, scalar12645, tp12645, tm12645, ep12645, em12645, dsL]
  · norm_num [world12645, agent12645, scalar12645, tp12645, tm12645, ep12645, em12645, dsL]
  · norm_num [world12645, agent12645, scalar12645, tp12645, tm12645, ep12645, em12645, dsL]
  · norm_num [world12645, agent12645, scalar12645, tp12645, tm12645, ep12645, em12645, dsL]
  · norm_num [world12645, agent12645, scalar12645, tp12645, tm12645, ep12645, em12645, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12645, agent12645, tp12645, tm12645, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12645, agent12645, tp12645, tm12645, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12645, agent12645, scalar12645, tp12645, tm12645, ep12645, em12645, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12645, agent12645, tp12645, tm12645, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12645, agent12645, scalar12645, tp12645, tm12645, ep12645, em12645, dsL]

theorem tails12645 :
    exp (-((12645:ℝ)*ep12645)) ≤ scalar12645.upperTail ∧
    exp (-((12645:ℝ)*em12645)) ≤ scalar12645.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12645:ℝ)) (by norm_num [ep12645]) ?_)
      (show bp12645^8 ≤ scalar12645.upperTail by norm_num [bp12645, scalar12645])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12645, bp12645, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12645:ℝ)) (by norm_num [em12645]) ?_)
      (show bm12645^8 ≤ scalar12645.lowerTail by norm_num [bm12645, scalar12645])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12645, bm12645, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12645 :
    agent12645.root+dsL+scalar12645.worldRadius < √(1/100/aL) ∧
    2*(agent12645.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12645, agent12645, scalar12645, tp12645, tm12645, ep12645, em12645, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12645, agent12645, scalar12645, tp12645, tm12645, ep12645, em12645, dsL]

noncomputable def master12645 : MasterCertificate 12645 world12645 agent12645 :=
  master scalar12645 dsL tp12645 tm12645 ep12645 em12645
    (by norm_num [dsL]) (by norm_num [tp12645]) (by norm_num [tm12645])
    (by norm_num [ep12645]) (by norm_num [em12645])
    positive12645 negative12645 tails12645.1 tails12645.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12645.1 tailGuards12645.2

theorem preserves12645 : master12645.toScalarCertificate = scalar12645 := rfl

noncomputable def tp12646 : ℝ := (2311393099 / 10000000000)
noncomputable def tm12646 : ℝ := (-((756446697 / 1250000000)))
noncomputable def ep12646 : ℝ := (51272940784803863 / 100000000000000000000)
noncomputable def em12646 : ℝ := (49977433694283089 / 100000000000000000000)
noncomputable def bp12646 : ℝ := (22231851080161669013 / 50000000000000000000)
noncomputable def bm12646 : ℝ := (45383649765827565021 / 100000000000000000000)

theorem positive12646 :
    Eplus aL (agent12646.root+dsL) scalar12646.worldRadius world12646.frame
      agent12646.frame tp12646 ≤ -ep12646 := by
  apply positive_check (eT := (115578580459936260123 / 100000000000000000000)) (y := (37822172235113113707 / 100000000000000000000)) (u := (145968655213302164753 / 100000000000000000000))
  · norm_num [world12646, agent12646, scalar12646, tp12646, tm12646, ep12646, em12646, dsL]
  · norm_num [world12646, agent12646, scalar12646, tp12646, tm12646, ep12646, em12646, dsL]
  · norm_num [world12646, agent12646, scalar12646, tp12646, tm12646, ep12646, em12646, dsL]
  · norm_num [world12646, agent12646, scalar12646, tp12646, tm12646, ep12646, em12646, dsL]
  · norm_num [world12646, agent12646, scalar12646, tp12646, tm12646, ep12646, em12646, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12646, agent12646, tp12646, tm12646, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12646, agent12646, scalar12646, tp12646, tm12646, ep12646, em12646, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12646, agent12646, tp12646, tm12646, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12646, agent12646, scalar12646, tp12646, tm12646, ep12646, em12646, dsL]

theorem negative12646 :
    Eminus aL (agent12646.root+dsL) scalar12646.worldRadius world12646.frame
      agent12646.frame tm12646 ≤ -em12646 := by
  apply negative_check (lo := (13690132545449506721 / 20000000000000000000)) (hi := (34225331363623766803 / 50000000000000000000))
    (y := (-((71694404720644147451 / 100000000000000000000)))) (u := (24412101152294765553 / 50000000000000000000))
  · norm_num [world12646, agent12646, scalar12646, tp12646, tm12646, ep12646, em12646, dsL]
  · norm_num [world12646, agent12646, scalar12646, tp12646, tm12646, ep12646, em12646, dsL]
  · norm_num [world12646, agent12646, scalar12646, tp12646, tm12646, ep12646, em12646, dsL]
  · norm_num [world12646, agent12646, scalar12646, tp12646, tm12646, ep12646, em12646, dsL]
  · norm_num [world12646, agent12646, scalar12646, tp12646, tm12646, ep12646, em12646, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12646, agent12646, tp12646, tm12646, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12646, agent12646, tp12646, tm12646, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12646, agent12646, scalar12646, tp12646, tm12646, ep12646, em12646, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12646, agent12646, tp12646, tm12646, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12646, agent12646, scalar12646, tp12646, tm12646, ep12646, em12646, dsL]

theorem tails12646 :
    exp (-((12646:ℝ)*ep12646)) ≤ scalar12646.upperTail ∧
    exp (-((12646:ℝ)*em12646)) ≤ scalar12646.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12646:ℝ)) (by norm_num [ep12646]) ?_)
      (show bp12646^8 ≤ scalar12646.upperTail by norm_num [bp12646, scalar12646])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12646, bp12646, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12646:ℝ)) (by norm_num [em12646]) ?_)
      (show bm12646^8 ≤ scalar12646.lowerTail by norm_num [bm12646, scalar12646])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12646, bm12646, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12646 :
    agent12646.root+dsL+scalar12646.worldRadius < √(1/100/aL) ∧
    2*(agent12646.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12646, agent12646, scalar12646, tp12646, tm12646, ep12646, em12646, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12646, agent12646, scalar12646, tp12646, tm12646, ep12646, em12646, dsL]

noncomputable def master12646 : MasterCertificate 12646 world12646 agent12646 :=
  master scalar12646 dsL tp12646 tm12646 ep12646 em12646
    (by norm_num [dsL]) (by norm_num [tp12646]) (by norm_num [tm12646])
    (by norm_num [ep12646]) (by norm_num [em12646])
    positive12646 negative12646 tails12646.1 tails12646.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12646.1 tailGuards12646.2

theorem preserves12646 : master12646.toScalarCertificate = scalar12646 := rfl

noncomputable def tp12647 : ℝ := (2311480343 / 10000000000)
noncomputable def tm12647 : ℝ := (-((378235081 / 625000000)))
noncomputable def ep12647 : ℝ := (12818907973900291 / 25000000000000000000)
noncomputable def em12647 : ℝ := (6247468281851253 / 12500000000000000000)
noncomputable def bp12647 : ℝ := (4445896105851957509 / 10000000000000000000)
noncomputable def bm12647 : ℝ := (45379155623587369059 / 100000000000000000000)

theorem positive12647 :
    Eplus aL (agent12647.root+dsL) scalar12647.worldRadius world12647.frame
      agent12647.frame tp12647 ≤ -ep12647 := by
  apply positive_check (eT := (115578839039786121363 / 100000000000000000000)) (y := (37822986345249343851 / 100000000000000000000)) (u := (145969843563757209267 / 100000000000000000000))
  · norm_num [world12647, agent12647, scalar12647, tp12647, tm12647, ep12647, em12647, dsL]
  · norm_num [world12647, agent12647, scalar12647, tp12647, tm12647, ep12647, em12647, dsL]
  · norm_num [world12647, agent12647, scalar12647, tp12647, tm12647, ep12647, em12647, dsL]
  · norm_num [world12647, agent12647, scalar12647, tp12647, tm12647, ep12647, em12647, dsL]
  · norm_num [world12647, agent12647, scalar12647, tp12647, tm12647, ep12647, em12647, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12647, agent12647, tp12647, tm12647, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12647, agent12647, scalar12647, tp12647, tm12647, ep12647, em12647, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12647, agent12647, tp12647, tm12647, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12647, agent12647, scalar12647, tp12647, tm12647, ep12647, em12647, dsL]

theorem negative12647 :
    Eminus aL (agent12647.root+dsL) scalar12647.worldRadius world12647.frame
      agent12647.frame tm12647 ≤ -em12647 := by
  apply negative_check (lo := (68450436270854669939 / 100000000000000000000)) (hi := (3422521813542733497 / 5000000000000000000))
    (y := (-((35847249792259063811 / 50000000000000000000)))) (u := (12206038997020438469 / 25000000000000000000))
  · norm_num [world12647, agent12647, scalar12647, tp12647, tm12647, ep12647, em12647, dsL]
  · norm_num [world12647, agent12647, scalar12647, tp12647, tm12647, ep12647, em12647, dsL]
  · norm_num [world12647, agent12647, scalar12647, tp12647, tm12647, ep12647, em12647, dsL]
  · norm_num [world12647, agent12647, scalar12647, tp12647, tm12647, ep12647, em12647, dsL]
  · norm_num [world12647, agent12647, scalar12647, tp12647, tm12647, ep12647, em12647, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12647, agent12647, tp12647, tm12647, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12647, agent12647, tp12647, tm12647, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12647, agent12647, scalar12647, tp12647, tm12647, ep12647, em12647, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12647, agent12647, tp12647, tm12647, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12647, agent12647, scalar12647, tp12647, tm12647, ep12647, em12647, dsL]

theorem tails12647 :
    exp (-((12647:ℝ)*ep12647)) ≤ scalar12647.upperTail ∧
    exp (-((12647:ℝ)*em12647)) ≤ scalar12647.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12647:ℝ)) (by norm_num [ep12647]) ?_)
      (show bp12647^8 ≤ scalar12647.upperTail by norm_num [bp12647, scalar12647])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12647, bp12647, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12647:ℝ)) (by norm_num [em12647]) ?_)
      (show bm12647^8 ≤ scalar12647.lowerTail by norm_num [bm12647, scalar12647])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12647, bm12647, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12647 :
    agent12647.root+dsL+scalar12647.worldRadius < √(1/100/aL) ∧
    2*(agent12647.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12647, agent12647, scalar12647, tp12647, tm12647, ep12647, em12647, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12647, agent12647, scalar12647, tp12647, tm12647, ep12647, em12647, dsL]

noncomputable def master12647 : MasterCertificate 12647 world12647 agent12647 :=
  master scalar12647 dsL tp12647 tm12647 ep12647 em12647
    (by norm_num [dsL]) (by norm_num [tp12647]) (by norm_num [tm12647])
    (by norm_num [ep12647]) (by norm_num [em12647])
    positive12647 negative12647 tails12647.1 tails12647.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12647.1 tailGuards12647.2

theorem preserves12647 : master12647.toScalarCertificate = scalar12647 := rfl

noncomputable def tp12648 : ℝ := (2311567603 / 10000000000)
noncomputable def tm12648 : ℝ := (-((756493597 / 1250000000)))
noncomputable def ep12648 : ℝ := (102556643139911 / 200000000000000000)
noncomputable def em12648 : ℝ := (49982057477925761 / 100000000000000000000)
noncomputable def bp12648 : ℝ := (2778388823296083423 / 6250000000000000000)
noncomputable def bm12648 : ℝ := (9074932524695263037 / 20000000000000000000)

theorem positive12648 :
    Eplus aL (agent12648.root+dsL) scalar12648.worldRadius world12648.frame
      agent12648.frame tp12648 ≤ -ep12648 := by
  apply positive_check (eT := (57789548884025154633 / 50000000000000000000)) (y := (37823801215690186439 / 100000000000000000000)) (u := (145971033033711267439 / 100000000000000000000))
  · norm_num [world12648, agent12648, scalar12648, tp12648, tm12648, ep12648, em12648, dsL]
  · norm_num [world12648, agent12648, scalar12648, tp12648, tm12648, ep12648, em12648, dsL]
  · norm_num [world12648, agent12648, scalar12648, tp12648, tm12648, ep12648, em12648, dsL]
  · norm_num [world12648, agent12648, scalar12648, tp12648, tm12648, ep12648, em12648, dsL]
  · norm_num [world12648, agent12648, scalar12648, tp12648, tm12648, ep12648, em12648, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12648, agent12648, tp12648, tm12648, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12648, agent12648, scalar12648, tp12648, tm12648, ep12648, em12648, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12648, agent12648, tp12648, tm12648, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12648, agent12648, scalar12648, tp12648, tm12648, ep12648, em12648, dsL]

theorem negative12648 :
    Eminus aL (agent12648.root+dsL) scalar12648.worldRadius world12648.frame
      agent12648.frame tm12648 ≤ -em12648 := by
  apply negative_check (lo := (68450210786773805139 / 100000000000000000000)) (hi := (3422510539338690257 / 5000000000000000000))
    (y := (-((71694592978238732217 / 100000000000000000000)))) (u := (1525753449668975499 / 3125000000000000000))
  · norm_num [world12648, agent12648, scalar12648, tp12648, tm12648, ep12648, em12648, dsL]
  · norm_num [world12648, agent12648, scalar12648, tp12648, tm12648, ep12648, em12648, dsL]
  · norm_num [world12648, agent12648, scalar12648, tp12648, tm12648, ep12648, em12648, dsL]
  · norm_num [world12648, agent12648, scalar12648, tp12648, tm12648, ep12648, em12648, dsL]
  · norm_num [world12648, agent12648, scalar12648, tp12648, tm12648, ep12648, em12648, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12648, agent12648, tp12648, tm12648, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12648, agent12648, tp12648, tm12648, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12648, agent12648, scalar12648, tp12648, tm12648, ep12648, em12648, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12648, agent12648, tp12648, tm12648, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12648, agent12648, scalar12648, tp12648, tm12648, ep12648, em12648, dsL]

theorem tails12648 :
    exp (-((12648:ℝ)*ep12648)) ≤ scalar12648.upperTail ∧
    exp (-((12648:ℝ)*em12648)) ≤ scalar12648.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12648:ℝ)) (by norm_num [ep12648]) ?_)
      (show bp12648^8 ≤ scalar12648.upperTail by norm_num [bp12648, scalar12648])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12648, bp12648, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12648:ℝ)) (by norm_num [em12648]) ?_)
      (show bm12648^8 ≤ scalar12648.lowerTail by norm_num [bm12648, scalar12648])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12648, bm12648, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12648 :
    agent12648.root+dsL+scalar12648.worldRadius < √(1/100/aL) ∧
    2*(agent12648.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12648, agent12648, scalar12648, tp12648, tm12648, ep12648, em12648, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12648, agent12648, scalar12648, tp12648, tm12648, ep12648, em12648, dsL]

noncomputable def master12648 : MasterCertificate 12648 world12648 agent12648 :=
  master scalar12648 dsL tp12648 tm12648 ep12648 em12648
    (by norm_num [dsL]) (by norm_num [tp12648]) (by norm_num [tm12648])
    (by norm_num [ep12648]) (by norm_num [em12648])
    positive12648 negative12648 tails12648.1 tails12648.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12648.1 tailGuards12648.2

theorem preserves12648 : master12648.toScalarCertificate = scalar12648 := rfl

noncomputable def tp12649 : ℝ := (1155827393 / 5000000000)
noncomputable def tm12649 : ℝ := (-((6052136081 / 10000000000)))
noncomputable def ep12649 : ℝ := (51281009496338183 / 100000000000000000000)
noncomputable def em12649 : ℝ := (49984367097999089 / 100000000000000000000)
noncomputable def bp12649 : ℝ := (5556185340234731881 / 12500000000000000000)
noncomputable def bm12649 : ℝ := (9074034191204758013 / 20000000000000000000)

theorem positive12649 :
    Eplus aL (agent12649.root+dsL) scalar12649.worldRadius world12649.frame
      agent12649.frame tp12649 ≤ -ep12649 := by
  apply positive_check (eT := (23115871194292304201 / 20000000000000000000)) (y := (3782461521069943599 / 10000000000000000000)) (u := (72986110617735528407 / 50000000000000000000))
  · norm_num [world12649, agent12649, scalar12649, tp12649, tm12649, ep12649, em12649, dsL]
  · norm_num [world12649, agent12649, scalar12649, tp12649, tm12649, ep12649, em12649, dsL]
  · norm_num [world12649, agent12649, scalar12649, tp12649, tm12649, ep12649, em12649, dsL]
  · norm_num [world12649, agent12649, scalar12649, tp12649, tm12649, ep12649, em12649, dsL]
  · norm_num [world12649, agent12649, scalar12649, tp12649, tm12649, ep12649, em12649, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12649, agent12649, tp12649, tm12649, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12649, agent12649, scalar12649, tp12649, tm12649, ep12649, em12649, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12649, agent12649, tp12649, tm12649, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12649, agent12649, scalar12649, tp12649, tm12649, ep12649, em12649, dsL]

theorem negative12649 :
    Eminus aL (agent12649.root+dsL) scalar12649.worldRadius world12649.frame
      agent12649.frame tm12649 ≤ -em12649 := by
  apply negative_check (lo := (17112496499071742587 / 25000000000000000000)) (hi := (68449985996286970349 / 100000000000000000000))
    (y := (-((71694685531596443441 / 100000000000000000000)))) (u := (61030081501343237 / 125000000000000000))
  · norm_num [world12649, agent12649, scalar12649, tp12649, tm12649, ep12649, em12649, dsL]
  · norm_num [world12649, agent12649, scalar12649, tp12649, tm12649, ep12649, em12649, dsL]
  · norm_num [world12649, agent12649, scalar12649, tp12649, tm12649, ep12649, em12649, dsL]
  · norm_num [world12649, agent12649, scalar12649, tp12649, tm12649, ep12649, em12649, dsL]
  · norm_num [world12649, agent12649, scalar12649, tp12649, tm12649, ep12649, em12649, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12649, agent12649, tp12649, tm12649, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12649, agent12649, tp12649, tm12649, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12649, agent12649, scalar12649, tp12649, tm12649, ep12649, em12649, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12649, agent12649, tp12649, tm12649, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12649, agent12649, scalar12649, tp12649, tm12649, ep12649, em12649, dsL]

theorem tails12649 :
    exp (-((12649:ℝ)*ep12649)) ≤ scalar12649.upperTail ∧
    exp (-((12649:ℝ)*em12649)) ≤ scalar12649.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12649:ℝ)) (by norm_num [ep12649]) ?_)
      (show bp12649^8 ≤ scalar12649.upperTail by norm_num [bp12649, scalar12649])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12649, bp12649, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12649:ℝ)) (by norm_num [em12649]) ?_)
      (show bm12649^8 ≤ scalar12649.lowerTail by norm_num [bm12649, scalar12649])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12649, bm12649, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12649 :
    agent12649.root+dsL+scalar12649.worldRadius < √(1/100/aL) ∧
    2*(agent12649.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12649, agent12649, scalar12649, tp12649, tm12649, ep12649, em12649, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12649, agent12649, scalar12649, tp12649, tm12649, ep12649, em12649, dsL]

noncomputable def master12649 : MasterCertificate 12649 world12649 agent12649 :=
  master scalar12649 dsL tp12649 tm12649 ep12649 em12649
    (by norm_num [dsL]) (by norm_num [tp12649]) (by norm_num [tm12649])
    (by norm_num [ep12649]) (by norm_num [em12649])
    positive12649 negative12649 tails12649.1 tails12649.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12649.1 tailGuards12649.2

theorem preserves12649 : master12649.toScalarCertificate = scalar12649 := rfl

end BstLean.Part268
