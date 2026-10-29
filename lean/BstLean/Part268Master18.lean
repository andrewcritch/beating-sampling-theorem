import BstLean.Part261Checker
import BstLean.Part268Scalar18
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12800 : ℝ := (2325587651 / 10000000000)
noncomputable def tm12800 : ℝ := (-((6083041943 / 10000000000)))
noncomputable def ep12800 : ℝ := (10339013782391699 / 20000000000000000000)
noncomputable def em12800 : ℝ := (201378268134037 / 400000000000000000)
noncomputable def bp12800 : ℝ := (10932660905412181159 / 25000000000000000000)
noncomputable def bm12800 : ℝ := (2234292984297058319 / 5000000000000000000)

theorem positive12800 :
    Eplus aL (agent12800.root+dsL) scalar12800.worldRadius world12800.frame
      agent12800.frame tp12800 ≤ -ep12800 := by
  apply positive_check (eT := (14453032327389280271 / 12500000000000000000)) (y := (37931682548860235617 / 100000000000000000000)) (u := (29225718700815375359 / 20000000000000000000))
  · norm_num [world12800, agent12800, scalar12800, tp12800, tm12800, ep12800, em12800, dsL]
  · norm_num [world12800, agent12800, scalar12800, tp12800, tm12800, ep12800, em12800, dsL]
  · norm_num [world12800, agent12800, scalar12800, tp12800, tm12800, ep12800, em12800, dsL]
  · norm_num [world12800, agent12800, scalar12800, tp12800, tm12800, ep12800, em12800, dsL]
  · norm_num [world12800, agent12800, scalar12800, tp12800, tm12800, ep12800, em12800, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12800, agent12800, tp12800, tm12800, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12800, agent12800, scalar12800, tp12800, tm12800, ep12800, em12800, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12800, agent12800, tp12800, tm12800, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12800, agent12800, scalar12800, tp12800, tm12800, ep12800, em12800, dsL]

theorem negative12800 :
    Eminus aL (agent12800.root+dsL) scalar12800.worldRadius world12800.frame
      agent12800.frame tm12800 ≤ -em12800 := by
  apply negative_check (lo := (34202100111645808077 / 50000000000000000000)) (hi := (13680840044658323231 / 20000000000000000000))
    (y := (-((71673902881786044537 / 100000000000000000000)))) (u := (9766842638008501779 / 20000000000000000000))
  · norm_num [world12800, agent12800, scalar12800, tp12800, tm12800, ep12800, em12800, dsL]
  · norm_num [world12800, agent12800, scalar12800, tp12800, tm12800, ep12800, em12800, dsL]
  · norm_num [world12800, agent12800, scalar12800, tp12800, tm12800, ep12800, em12800, dsL]
  · norm_num [world12800, agent12800, scalar12800, tp12800, tm12800, ep12800, em12800, dsL]
  · norm_num [world12800, agent12800, scalar12800, tp12800, tm12800, ep12800, em12800, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12800, agent12800, tp12800, tm12800, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12800, agent12800, tp12800, tm12800, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12800, agent12800, scalar12800, tp12800, tm12800, ep12800, em12800, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12800, agent12800, tp12800, tm12800, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12800, agent12800, scalar12800, tp12800, tm12800, ep12800, em12800, dsL]

theorem tails12800 :
    exp (-((12800:ℝ)*ep12800)) ≤ scalar12800.upperTail ∧
    exp (-((12800:ℝ)*em12800)) ≤ scalar12800.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12800:ℝ)) (by norm_num [ep12800]) ?_)
      (show bp12800^8 ≤ scalar12800.upperTail by norm_num [bp12800, scalar12800])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12800, bp12800, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12800:ℝ)) (by norm_num [em12800]) ?_)
      (show bm12800^8 ≤ scalar12800.lowerTail by norm_num [bm12800, scalar12800])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12800, bm12800, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12800 :
    agent12800.root+dsL+scalar12800.worldRadius < √(1/100/aL) ∧
    2*(agent12800.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12800, agent12800, scalar12800, tp12800, tm12800, ep12800, em12800, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12800, agent12800, scalar12800, tp12800, tm12800, ep12800, em12800, dsL]

noncomputable def master12800 : MasterCertificate 12800 world12800 agent12800 :=
  master scalar12800 dsL tp12800 tm12800 ep12800 em12800
    (by norm_num [dsL]) (by norm_num [tp12800]) (by norm_num [tm12800])
    (by norm_num [ep12800]) (by norm_num [em12800])
    positive12800 negative12800 tails12800.1 tails12800.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12800.1 tailGuards12800.2

theorem preserves12800 : master12800.toScalarCertificate = scalar12800 := rfl

noncomputable def tp12801 : ℝ := (2325669479 / 10000000000)
noncomputable def tm12801 : ℝ := (-((1520804261 / 2500000000)))
noncomputable def ep12801 : ℝ := (10339514107093069 / 20000000000000000000)
noncomputable def em12801 : ℝ := (6293338351086783 / 12500000000000000000)
noncomputable def bp12801 : ℝ := (136643961060479203 / 312500000000000000)
noncomputable def bm12801 : ℝ := (22340758890725794357 / 50000000000000000000)

theorem positive12801 :
    Eplus aL (agent12801.root+dsL) scalar12801.worldRadius world12801.frame
      agent12801.frame tp12801 ≤ -ep12801 := by
  apply positive_check (eT := (1445306036492726071 / 1250000000000000000)) (y := (37932438436049100157 / 100000000000000000000)) (u := (73064849037784546997 / 50000000000000000000))
  · norm_num [world12801, agent12801, scalar12801, tp12801, tm12801, ep12801, em12801, dsL]
  · norm_num [world12801, agent12801, scalar12801, tp12801, tm12801, ep12801, em12801, dsL]
  · norm_num [world12801, agent12801, scalar12801, tp12801, tm12801, ep12801, em12801, dsL]
  · norm_num [world12801, agent12801, scalar12801, tp12801, tm12801, ep12801, em12801, dsL]
  · norm_num [world12801, agent12801, scalar12801, tp12801, tm12801, ep12801, em12801, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12801, agent12801, tp12801, tm12801, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12801, agent12801, scalar12801, tp12801, tm12801, ep12801, em12801, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12801, agent12801, tp12801, tm12801, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12801, agent12801, scalar12801, tp12801, tm12801, ep12801, em12801, dsL]

theorem negative12801 :
    Eminus aL (agent12801.root+dsL) scalar12801.worldRadius world12801.frame
      agent12801.frame tm12801 ≤ -em12801 := by
  apply negative_check (lo := (68404019387765980013 / 100000000000000000000)) (hi := (34202009693882990007 / 50000000000000000000))
    (y := (-((71673934188244553727 / 100000000000000000000)))) (u := (12208549475445552843 / 25000000000000000000))
  · norm_num [world12801, agent12801, scalar12801, tp12801, tm12801, ep12801, em12801, dsL]
  · norm_num [world12801, agent12801, scalar12801, tp12801, tm12801, ep12801, em12801, dsL]
  · norm_num [world12801, agent12801, scalar12801, tp12801, tm12801, ep12801, em12801, dsL]
  · norm_num [world12801, agent12801, scalar12801, tp12801, tm12801, ep12801, em12801, dsL]
  · norm_num [world12801, agent12801, scalar12801, tp12801, tm12801, ep12801, em12801, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12801, agent12801, tp12801, tm12801, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12801, agent12801, tp12801, tm12801, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12801, agent12801, scalar12801, tp12801, tm12801, ep12801, em12801, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12801, agent12801, tp12801, tm12801, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12801, agent12801, scalar12801, tp12801, tm12801, ep12801, em12801, dsL]

theorem tails12801 :
    exp (-((12801:ℝ)*ep12801)) ≤ scalar12801.upperTail ∧
    exp (-((12801:ℝ)*em12801)) ≤ scalar12801.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12801:ℝ)) (by norm_num [ep12801]) ?_)
      (show bp12801^8 ≤ scalar12801.upperTail by norm_num [bp12801, scalar12801])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12801, bp12801, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12801:ℝ)) (by norm_num [em12801]) ?_)
      (show bm12801^8 ≤ scalar12801.lowerTail by norm_num [bm12801, scalar12801])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12801, bm12801, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12801 :
    agent12801.root+dsL+scalar12801.worldRadius < √(1/100/aL) ∧
    2*(agent12801.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12801, agent12801, scalar12801, tp12801, tm12801, ep12801, em12801, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12801, agent12801, scalar12801, tp12801, tm12801, ep12801, em12801, dsL]

noncomputable def master12801 : MasterCertificate 12801 world12801 agent12801 :=
  master scalar12801 dsL tp12801 tm12801 ep12801 em12801
    (by norm_num [dsL]) (by norm_num [tp12801]) (by norm_num [tm12801])
    (by norm_num [ep12801]) (by norm_num [em12801])
    positive12801 negative12801 tails12801.1 tails12801.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12801.1 tailGuards12801.2

theorem preserves12801 : master12801.toScalarCertificate = scalar12801 := rfl

noncomputable def tp12802 : ℝ := (2325751313 / 10000000000)
noncomputable def tm12802 : ℝ := (-((6083392017 / 10000000000)))
noncomputable def ep12802 : ℝ := (25850035794926023 / 50000000000000000000)
noncomputable def em12802 : ℝ := (12587211520466879 / 25000000000000000000)
noncomputable def bp12802 : ℝ := (5465186507582553853 / 12500000000000000000)
noncomputable def bm12802 : ℝ := (44677176418757222081 / 100000000000000000000)

theorem positive12802 :
    Eplus aL (agent12802.root+dsL) scalar12802.worldRadius world12802.frame
      agent12802.frame tp12802 ≤ -ep12802 := by
  apply positive_check (eT := (115624707295904411181 / 100000000000000000000)) (y := (37933194528383676029 / 100000000000000000000)) (u := (146130802955191732041 / 100000000000000000000))
  · norm_num [world12802, agent12802, scalar12802, tp12802, tm12802, ep12802, em12802, dsL]
  · norm_num [world12802, agent12802, scalar12802, tp12802, tm12802, ep12802, em12802, dsL]
  · norm_num [world12802, agent12802, scalar12802, tp12802, tm12802, ep12802, em12802, dsL]
  · norm_num [world12802, agent12802, scalar12802, tp12802, tm12802, ep12802, em12802, dsL]
  · norm_num [world12802, agent12802, scalar12802, tp12802, tm12802, ep12802, em12802, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12802, agent12802, tp12802, tm12802, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12802, agent12802, scalar12802, tp12802, tm12802, ep12802, em12802, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12802, agent12802, tp12802, tm12802, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12802, agent12802, scalar12802, tp12802, tm12802, ep12802, em12802, dsL]

theorem negative12802 :
    Eminus aL (agent12802.root+dsL) scalar12802.worldRadius world12802.frame
      agent12802.frame tm12802 ≤ -em12802 := by
  apply negative_check (lo := (3420191952090692421 / 5000000000000000000)) (hi := (68403839041813848421 / 100000000000000000000))
    (y := (-((71673964625496370989 / 100000000000000000000)))) (u := (4883418303799668513 / 10000000000000000000))
  · norm_num [world12802, agent12802, scalar12802, tp12802, tm12802, ep12802, em12802, dsL]
  · norm_num [world12802, agent12802, scalar12802, tp12802, tm12802, ep12802, em12802, dsL]
  · norm_num [world12802, agent12802, scalar12802, tp12802, tm12802, ep12802, em12802, dsL]
  · norm_num [world12802, agent12802, scalar12802, tp12802, tm12802, ep12802, em12802, dsL]
  · norm_num [world12802, agent12802, scalar12802, tp12802, tm12802, ep12802, em12802, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12802, agent12802, tp12802, tm12802, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12802, agent12802, tp12802, tm12802, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12802, agent12802, scalar12802, tp12802, tm12802, ep12802, em12802, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12802, agent12802, tp12802, tm12802, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12802, agent12802, scalar12802, tp12802, tm12802, ep12802, em12802, dsL]

theorem tails12802 :
    exp (-((12802:ℝ)*ep12802)) ≤ scalar12802.upperTail ∧
    exp (-((12802:ℝ)*em12802)) ≤ scalar12802.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12802:ℝ)) (by norm_num [ep12802]) ?_)
      (show bp12802^8 ≤ scalar12802.upperTail by norm_num [bp12802, scalar12802])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12802, bp12802, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12802:ℝ)) (by norm_num [em12802]) ?_)
      (show bm12802^8 ≤ scalar12802.lowerTail by norm_num [bm12802, scalar12802])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12802, bm12802, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12802 :
    agent12802.root+dsL+scalar12802.worldRadius < √(1/100/aL) ∧
    2*(agent12802.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12802, agent12802, scalar12802, tp12802, tm12802, ep12802, em12802, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12802, agent12802, scalar12802, tp12802, tm12802, ep12802, em12802, dsL]

noncomputable def master12802 : MasterCertificate 12802 world12802 agent12802 :=
  master scalar12802 dsL tp12802 tm12802 ep12802 em12802
    (by norm_num [dsL]) (by norm_num [tp12802]) (by norm_num [tm12802])
    (by norm_num [ep12802]) (by norm_num [em12802])
    positive12802 negative12802 tails12802.1 tails12802.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12802.1 tailGuards12802.2

theorem preserves12802 : master12802.toScalarCertificate = scalar12802 := rfl

noncomputable def tp12803 : ℝ := (581458261 / 2500000000)
noncomputable def tm12803 : ℝ := (-((6083566871 / 10000000000)))
noncomputable def ep12803 : ℝ := (12925642480670709 / 25000000000000000000)
noncomputable def em12803 : ℝ := (6293872854008739 / 12500000000000000000)
noncomputable def bp12803 : ℝ := (21858459345746300703 / 50000000000000000000)
noncomputable def bm12803 : ℝ := (11168209260679093517 / 25000000000000000000)

theorem positive12803 :
    Eplus aL (agent12803.root+dsL) scalar12803.worldRadius world12803.frame
      agent12803.frame tp12803 ≤ -ep12803 := by
  apply positive_check (eT := (115624930961847692327 / 100000000000000000000)) (y := (4741743689706878617 / 12500000000000000000)) (u := (146131906231240988257 / 100000000000000000000))
  · norm_num [world12803, agent12803, scalar12803, tp12803, tm12803, ep12803, em12803, dsL]
  · norm_num [world12803, agent12803, scalar12803, tp12803, tm12803, ep12803, em12803, dsL]
  · norm_num [world12803, agent12803, scalar12803, tp12803, tm12803, ep12803, em12803, dsL]
  · norm_num [world12803, agent12803, scalar12803, tp12803, tm12803, ep12803, em12803, dsL]
  · norm_num [world12803, agent12803, scalar12803, tp12803, tm12803, ep12803, em12803, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12803, agent12803, tp12803, tm12803, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12803, agent12803, scalar12803, tp12803, tm12803, ep12803, em12803, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12803, agent12803, tp12803, tm12803, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12803, agent12803, scalar12803, tp12803, tm12803, ep12803, em12803, dsL]

theorem negative12803 :
    Eminus aL (agent12803.root+dsL) scalar12803.worldRadius world12803.frame
      agent12803.frame tm12803 ≤ -em12803 := by
  apply negative_check (lo := (34201829573500417571 / 50000000000000000000)) (hi := (68403659147000835143 / 100000000000000000000))
    (y := (-((1119906168031974579 / 1562500000000000000)))) (u := (24417084162483823419 / 50000000000000000000))
  · norm_num [world12803, agent12803, scalar12803, tp12803, tm12803, ep12803, em12803, dsL]
  · norm_num [world12803, agent12803, scalar12803, tp12803, tm12803, ep12803, em12803, dsL]
  · norm_num [world12803, agent12803, scalar12803, tp12803, tm12803, ep12803, em12803, dsL]
  · norm_num [world12803, agent12803, scalar12803, tp12803, tm12803, ep12803, em12803, dsL]
  · norm_num [world12803, agent12803, scalar12803, tp12803, tm12803, ep12803, em12803, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12803, agent12803, tp12803, tm12803, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12803, agent12803, tp12803, tm12803, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12803, agent12803, scalar12803, tp12803, tm12803, ep12803, em12803, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12803, agent12803, tp12803, tm12803, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12803, agent12803, scalar12803, tp12803, tm12803, ep12803, em12803, dsL]

theorem tails12803 :
    exp (-((12803:ℝ)*ep12803)) ≤ scalar12803.upperTail ∧
    exp (-((12803:ℝ)*em12803)) ≤ scalar12803.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12803:ℝ)) (by norm_num [ep12803]) ?_)
      (show bp12803^8 ≤ scalar12803.upperTail by norm_num [bp12803, scalar12803])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12803, bp12803, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12803:ℝ)) (by norm_num [em12803]) ?_)
      (show bm12803^8 ≤ scalar12803.lowerTail by norm_num [bm12803, scalar12803])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12803, bm12803, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12803 :
    agent12803.root+dsL+scalar12803.worldRadius < √(1/100/aL) ∧
    2*(agent12803.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12803, agent12803, scalar12803, tp12803, tm12803, ep12803, em12803, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12803, agent12803, scalar12803, tp12803, tm12803, ep12803, em12803, dsL]

noncomputable def master12803 : MasterCertificate 12803 world12803 agent12803 :=
  master scalar12803 dsL tp12803 tm12803 ep12803 em12803
    (by norm_num [dsL]) (by norm_num [tp12803]) (by norm_num [tm12803])
    (by norm_num [ep12803]) (by norm_num [em12803])
    positive12803 negative12803 tails12803.1 tails12803.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12803.1 tailGuards12803.2

theorem preserves12803 : master12803.toScalarCertificate = scalar12803 := rfl

noncomputable def tp12804 : ℝ := (116295741 / 500000000)
noncomputable def tm12804 : ℝ := (-((760467701 / 1250000000)))
noncomputable def ep12804 : ℝ := (25852533924055459 / 50000000000000000000)
noncomputable def em12804 : ℝ := (10070623838157639 / 20000000000000000000)
noncomputable def bp12804 : ℝ := (43712345812715281973 / 100000000000000000000)
noncomputable def bm12804 : ℝ := (44668498129413646583 / 100000000000000000000)

theorem positive12804 :
    Eplus aL (agent12804.root+dsL) scalar12804.worldRadius world12804.frame
      agent12804.frame tp12804 ≤ -ep12804 := by
  apply positive_check (eT := (14453144373182551569 / 12500000000000000000)) (y := (1517388221916289627 / 4000000000000000000)) (u := (146133011036836557133 / 100000000000000000000))
  · norm_num [world12804, agent12804, scalar12804, tp12804, tm12804, ep12804, em12804, dsL]
  · norm_num [world12804, agent12804, scalar12804, tp12804, tm12804, ep12804, em12804, dsL]
  · norm_num [world12804, agent12804, scalar12804, tp12804, tm12804, ep12804, em12804, dsL]
  · norm_num [world12804, agent12804, scalar12804, tp12804, tm12804, ep12804, em12804, dsL]
  · norm_num [world12804, agent12804, scalar12804, tp12804, tm12804, ep12804, em12804, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12804, agent12804, tp12804, tm12804, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12804, agent12804, scalar12804, tp12804, tm12804, ep12804, em12804, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12804, agent12804, tp12804, tm12804, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12804, agent12804, scalar12804, tp12804, tm12804, ep12804, em12804, dsL]

theorem negative12804 :
    Eminus aL (agent12804.root+dsL) scalar12804.worldRadius world12804.frame
      agent12804.frame tm12804 ≤ -em12804 := by
  apply negative_check (lo := (34201739847371443181 / 50000000000000000000)) (hi := (68403479694742886363 / 100000000000000000000))
    (y := (-((35837012204736337591 / 50000000000000000000)))) (u := (48834153842988996317 / 100000000000000000000))
  · norm_num [world12804, agent12804, scalar12804, tp12804, tm12804, ep12804, em12804, dsL]
  · norm_num [world12804, agent12804, scalar12804, tp12804, tm12804, ep12804, em12804, dsL]
  · norm_num [world12804, agent12804, scalar12804, tp12804, tm12804, ep12804, em12804, dsL]
  · norm_num [world12804, agent12804, scalar12804, tp12804, tm12804, ep12804, em12804, dsL]
  · norm_num [world12804, agent12804, scalar12804, tp12804, tm12804, ep12804, em12804, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12804, agent12804, tp12804, tm12804, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12804, agent12804, tp12804, tm12804, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12804, agent12804, scalar12804, tp12804, tm12804, ep12804, em12804, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12804, agent12804, tp12804, tm12804, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12804, agent12804, scalar12804, tp12804, tm12804, ep12804, em12804, dsL]

theorem tails12804 :
    exp (-((12804:ℝ)*ep12804)) ≤ scalar12804.upperTail ∧
    exp (-((12804:ℝ)*em12804)) ≤ scalar12804.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12804:ℝ)) (by norm_num [ep12804]) ?_)
      (show bp12804^8 ≤ scalar12804.upperTail by norm_num [bp12804, scalar12804])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12804, bp12804, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12804:ℝ)) (by norm_num [em12804]) ?_)
      (show bm12804^8 ≤ scalar12804.lowerTail by norm_num [bm12804, scalar12804])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12804, bm12804, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12804 :
    agent12804.root+dsL+scalar12804.worldRadius < √(1/100/aL) ∧
    2*(agent12804.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12804, agent12804, scalar12804, tp12804, tm12804, ep12804, em12804, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12804, agent12804, scalar12804, tp12804, tm12804, ep12804, em12804, dsL]

noncomputable def master12804 : MasterCertificate 12804 world12804 agent12804 :=
  master scalar12804 dsL tp12804 tm12804 ep12804 em12804
    (by norm_num [dsL]) (by norm_num [tp12804]) (by norm_num [tm12804])
    (by norm_num [ep12804]) (by norm_num [em12804])
    positive12804 negative12804 tails12804.1 tails12804.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12804.1 tailGuards12804.2

theorem preserves12804 : master12804.toScalarCertificate = scalar12804 := rfl

noncomputable def tp12805 : ℝ := (465199311 / 2000000000)
noncomputable def tm12805 : ℝ := (-((6083916289 / 10000000000)))
noncomputable def ep12805 : ℝ := (51707564588423381 / 100000000000000000000)
noncomputable def em12805 : ℝ := (10071050892087237 / 20000000000000000000)
noncomputable def bp12805 : ℝ := (21853886984213744599 / 50000000000000000000)
noncomputable def bm12805 : ℝ := (223320800887849961 / 500000000000000000)

theorem positive12805 :
    Eplus aL (agent12805.root+dsL) scalar12805.worldRadius world12805.frame
      agent12805.frame tp12805 ≤ -ep12805 := by
  apply positive_check (eT := (28906344686506586851 / 25000000000000000000)) (y := (37935461160247104287 / 100000000000000000000)) (u := (18266764405009038553 / 12500000000000000000))
  · norm_num [world12805, agent12805, scalar12805, tp12805, tm12805, ep12805, em12805, dsL]
  · norm_num [world12805, agent12805, scalar12805, tp12805, tm12805, ep12805, em12805, dsL]
  · norm_num [world12805, agent12805, scalar12805, tp12805, tm12805, ep12805, em12805, dsL]
  · norm_num [world12805, agent12805, scalar12805, tp12805, tm12805, ep12805, em12805, dsL]
  · norm_num [world12805, agent12805, scalar12805, tp12805, tm12805, ep12805, em12805, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12805, agent12805, tp12805, tm12805, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12805, agent12805, scalar12805, tp12805, tm12805, ep12805, em12805, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12805, agent12805, tp12805, tm12805, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12805, agent12805, scalar12805, tp12805, tm12805, ep12805, em12805, dsL]

theorem negative12805 :
    Eminus aL (agent12805.root+dsL) scalar12805.worldRadius world12805.frame
      agent12805.frame tm12805 ≤ -em12805 := by
  apply negative_check (lo := (68403300424590044457 / 100000000000000000000)) (hi := (34201650212295022229 / 50000000000000000000))
    (y := (-((71674054051233920097 / 100000000000000000000)))) (u := (48834139367687853571 / 100000000000000000000))
  · norm_num [world12805, agent12805, scalar12805, tp12805, tm12805, ep12805, em12805, dsL]
  · norm_num [world12805, agent12805, scalar12805, tp12805, tm12805, ep12805, em12805, dsL]
  · norm_num [world12805, agent12805, scalar12805, tp12805, tm12805, ep12805, em12805, dsL]
  · norm_num [world12805, agent12805, scalar12805, tp12805, tm12805, ep12805, em12805, dsL]
  · norm_num [world12805, agent12805, scalar12805, tp12805, tm12805, ep12805, em12805, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12805, agent12805, tp12805, tm12805, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12805, agent12805, tp12805, tm12805, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12805, agent12805, scalar12805, tp12805, tm12805, ep12805, em12805, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12805, agent12805, tp12805, tm12805, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12805, agent12805, scalar12805, tp12805, tm12805, ep12805, em12805, dsL]

theorem tails12805 :
    exp (-((12805:ℝ)*ep12805)) ≤ scalar12805.upperTail ∧
    exp (-((12805:ℝ)*em12805)) ≤ scalar12805.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12805:ℝ)) (by norm_num [ep12805]) ?_)
      (show bp12805^8 ≤ scalar12805.upperTail by norm_num [bp12805, scalar12805])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12805, bp12805, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12805:ℝ)) (by norm_num [em12805]) ?_)
      (show bm12805^8 ≤ scalar12805.lowerTail by norm_num [bm12805, scalar12805])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12805, bm12805, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12805 :
    agent12805.root+dsL+scalar12805.worldRadius < √(1/100/aL) ∧
    2*(agent12805.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12805, agent12805, scalar12805, tp12805, tm12805, ep12805, em12805, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12805, agent12805, scalar12805, tp12805, tm12805, ep12805, em12805, dsL]

noncomputable def master12805 : MasterCertificate 12805 world12805 agent12805 :=
  master scalar12805 dsL tp12805 tm12805 ep12805 em12805
    (by norm_num [dsL]) (by norm_num [tp12805]) (by norm_num [tm12805])
    (by norm_num [ep12805]) (by norm_num [em12805])
    positive12805 negative12805 tails12805.1 tails12805.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12805.1 tailGuards12805.2

theorem preserves12805 : master12805.toScalarCertificate = scalar12805 := rfl

noncomputable def tp12806 : ℝ := (145379889 / 625000000)
noncomputable def tm12806 : ℝ := (-((6084091061 / 10000000000)))
noncomputable def ep12806 : ℝ := (10342012001163869 / 20000000000000000000)
noncomputable def em12806 : ℝ := (50357388496229089 / 100000000000000000000)
noncomputable def bp12806 : ℝ := (21851601627500757323 / 50000000000000000000)
noncomputable def bm12806 : ℝ := (22329911645337521451 / 50000000000000000000)

theorem positive12806 :
    Eplus aL (agent12806.root+dsL) scalar12806.worldRadius world12806.frame
      agent12806.frame tp12806 ≤ -ep12806 := by
  apply positive_check (eT := (14453200257889624929 / 12500000000000000000)) (y := (18968108034169632457 / 50000000000000000000)) (u := (146135218422497664527 / 100000000000000000000))
  · norm_num [world12806, agent12806, scalar12806, tp12806, tm12806, ep12806, em12806, dsL]
  · norm_num [world12806, agent12806, scalar12806, tp12806, tm12806, ep12806, em12806, dsL]
  · norm_num [world12806, agent12806, scalar12806, tp12806, tm12806, ep12806, em12806, dsL]
  · norm_num [world12806, agent12806, scalar12806, tp12806, tm12806, ep12806, em12806, dsL]
  · norm_num [world12806, agent12806, scalar12806, tp12806, tm12806, ep12806, em12806, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12806, agent12806, tp12806, tm12806, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12806, agent12806, scalar12806, tp12806, tm12806, ep12806, em12806, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12806, agent12806, tp12806, tm12806, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12806, agent12806, scalar12806, tp12806, tm12806, ep12806, em12806, dsL]

theorem negative12806 :
    Eminus aL (agent12806.root+dsL) scalar12806.worldRadius world12806.frame
      agent12806.frame tm12806 ≤ -em12806 := by
  apply negative_check (lo := (34201560354469157279 / 50000000000000000000)) (hi := (68403120708938314559 / 100000000000000000000))
    (y := (-((4479630336852569993 / 6250000000000000000)))) (u := (48834124063848804001 / 100000000000000000000))
  · norm_num [world12806, agent12806, scalar12806, tp12806, tm12806, ep12806, em12806, dsL]
  · norm_num [world12806, agent12806, scalar12806, tp12806, tm12806, ep12806, em12806, dsL]
  · norm_num [world12806, agent12806, scalar12806, tp12806, tm12806, ep12806, em12806, dsL]
  · norm_num [world12806, agent12806, scalar12806, tp12806, tm12806, ep12806, em12806, dsL]
  · norm_num [world12806, agent12806, scalar12806, tp12806, tm12806, ep12806, em12806, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12806, agent12806, tp12806, tm12806, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12806, agent12806, tp12806, tm12806, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12806, agent12806, scalar12806, tp12806, tm12806, ep12806, em12806, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12806, agent12806, tp12806, tm12806, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12806, agent12806, scalar12806, tp12806, tm12806, ep12806, em12806, dsL]

theorem tails12806 :
    exp (-((12806:ℝ)*ep12806)) ≤ scalar12806.upperTail ∧
    exp (-((12806:ℝ)*em12806)) ≤ scalar12806.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12806:ℝ)) (by norm_num [ep12806]) ?_)
      (show bp12806^8 ≤ scalar12806.upperTail by norm_num [bp12806, scalar12806])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12806, bp12806, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12806:ℝ)) (by norm_num [em12806]) ?_)
      (show bm12806^8 ≤ scalar12806.lowerTail by norm_num [bm12806, scalar12806])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12806, bm12806, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12806 :
    agent12806.root+dsL+scalar12806.worldRadius < √(1/100/aL) ∧
    2*(agent12806.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12806, agent12806, scalar12806, tp12806, tm12806, ep12806, em12806, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12806, agent12806, scalar12806, tp12806, tm12806, ep12806, em12806, dsL]

noncomputable def master12806 : MasterCertificate 12806 world12806 agent12806 :=
  master scalar12806 dsL tp12806 tm12806 ep12806 em12806
    (by norm_num [dsL]) (by norm_num [tp12806]) (by norm_num [tm12806])
    (by norm_num [ep12806]) (by norm_num [em12806])
    positive12806 negative12806 tails12806.1 tails12806.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12806.1 tailGuards12806.2

theorem preserves12806 : master12806.toScalarCertificate = scalar12806 := rfl

noncomputable def tp12807 : ℝ := (581539963 / 2500000000)
noncomputable def tm12807 : ℝ := (-((380266581 / 625000000)))
noncomputable def ep12807 : ℝ := (6464069164719971 / 12500000000000000000)
noncomputable def em12807 : ℝ := (2014380823858901 / 4000000000000000000)
noncomputable def bp12807 : ℝ := (8739726843966555197 / 20000000000000000000)
noncomputable def bm12807 : ℝ := (44655487970333258933 / 100000000000000000000)

theorem positive12807 :
    Eplus aL (agent12807.root+dsL) scalar12807.worldRadius world12807.frame
      agent12807.frame tp12807 ≤ -ep12807 := by
  apply positive_check (eT := (115625825117215963409 / 100000000000000000000)) (y := (9484242689558594217 / 25000000000000000000)) (u := (146136321294385925013 / 100000000000000000000))
  · norm_num [world12807, agent12807, scalar12807, tp12807, tm12807, ep12807, em12807, dsL]
  · norm_num [world12807, agent12807, scalar12807, tp12807, tm12807, ep12807, em12807, dsL]
  · norm_num [world12807, agent12807, scalar12807, tp12807, tm12807, ep12807, em12807, dsL]
  · norm_num [world12807, agent12807, scalar12807, tp12807, tm12807, ep12807, em12807, dsL]
  · norm_num [world12807, agent12807, scalar12807, tp12807, tm12807, ep12807, em12807, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12807, agent12807, tp12807, tm12807, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12807, agent12807, scalar12807, tp12807, tm12807, ep12807, em12807, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12807, agent12807, tp12807, tm12807, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12807, agent12807, scalar12807, tp12807, tm12807, ep12807, em12807, dsL]

theorem negative12807 :
    Eminus aL (agent12807.root+dsL) scalar12807.worldRadius world12807.frame
      agent12807.frame tm12807 ≤ -em12807 := by
  apply negative_check (lo := (68402943228966073441 / 100000000000000000000)) (hi := (34201471614483036721 / 50000000000000000000))
    (y := (-((17918528052745183357 / 25000000000000000000)))) (u := (3052131935367768629 / 6250000000000000000))
  · norm_num [world12807, agent12807, scalar12807, tp12807, tm12807, ep12807, em12807, dsL]
  · norm_num [world12807, agent12807, scalar12807, tp12807, tm12807, ep12807, em12807, dsL]
  · norm_num [world12807, agent12807, scalar12807, tp12807, tm12807, ep12807, em12807, dsL]
  · norm_num [world12807, agent12807, scalar12807, tp12807, tm12807, ep12807, em12807, dsL]
  · norm_num [world12807, agent12807, scalar12807, tp12807, tm12807, ep12807, em12807, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12807, agent12807, tp12807, tm12807, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12807, agent12807, tp12807, tm12807, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12807, agent12807, scalar12807, tp12807, tm12807, ep12807, em12807, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12807, agent12807, tp12807, tm12807, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12807, agent12807, scalar12807, tp12807, tm12807, ep12807, em12807, dsL]

theorem tails12807 :
    exp (-((12807:ℝ)*ep12807)) ≤ scalar12807.upperTail ∧
    exp (-((12807:ℝ)*em12807)) ≤ scalar12807.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12807:ℝ)) (by norm_num [ep12807]) ?_)
      (show bp12807^8 ≤ scalar12807.upperTail by norm_num [bp12807, scalar12807])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12807, bp12807, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12807:ℝ)) (by norm_num [em12807]) ?_)
      (show bm12807^8 ≤ scalar12807.lowerTail by norm_num [bm12807, scalar12807])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12807, bm12807, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12807 :
    agent12807.root+dsL+scalar12807.worldRadius < √(1/100/aL) ∧
    2*(agent12807.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12807, agent12807, scalar12807, tp12807, tm12807, ep12807, em12807, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12807, agent12807, scalar12807, tp12807, tm12807, ep12807, em12807, dsL]

noncomputable def master12807 : MasterCertificate 12807 world12807 agent12807 :=
  master scalar12807 dsL tp12807 tm12807 ep12807 em12807
    (by norm_num [dsL]) (by norm_num [tp12807]) (by norm_num [tm12807])
    (by norm_num [ep12807]) (by norm_num [em12807])
    positive12807 negative12807 tails12807.1 tails12807.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12807.1 tailGuards12807.2

theorem preserves12807 : master12807.toScalarCertificate = scalar12807 := rfl

noncomputable def tp12808 : ℝ := (2326241427 / 10000000000)
noncomputable def tm12808 : ℝ := (-((3042219939 / 5000000000)))
noncomputable def ep12808 : ℝ := (6312871853909 / 12207031250000000)
noncomputable def em12808 : ℝ := (25180826154793419 / 50000000000000000000)
noncomputable def bp12808 : ℝ := (43694065671535265153 / 100000000000000000000)
noncomputable def bm12808 : ℝ := (22325576554791399917 / 50000000000000000000)

theorem positive12808 :
    Eplus aL (agent12808.root+dsL) scalar12808.worldRadius world12808.frame
      agent12808.frame tp12808 ≤ -ep12808 := by
  apply positive_check (eT := (115626047821692571481 / 100000000000000000000)) (y := (18968862385702548507 / 50000000000000000000)) (u := (146137423185649888001 / 100000000000000000000))
  · norm_num [world12808, agent12808, scalar12808, tp12808, tm12808, ep12808, em12808, dsL]
  · norm_num [world12808, agent12808, scalar12808, tp12808, tm12808, ep12808, em12808, dsL]
  · norm_num [world12808, agent12808, scalar12808, tp12808, tm12808, ep12808, em12808, dsL]
  · norm_num [world12808, agent12808, scalar12808, tp12808, tm12808, ep12808, em12808, dsL]
  · norm_num [world12808, agent12808, scalar12808, tp12808, tm12808, ep12808, em12808, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12808, agent12808, tp12808, tm12808, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12808, agent12808, scalar12808, tp12808, tm12808, ep12808, em12808, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12808, agent12808, tp12808, tm12808, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12808, agent12808, scalar12808, tp12808, tm12808, ep12808, em12808, dsL]

theorem negative12808 :
    Eminus aL (agent12808.root+dsL) scalar12808.worldRadius world12808.frame
      agent12808.frame tm12808 ≤ -em12808 := by
  apply negative_check (lo := (17100691052625462593 / 25000000000000000000)) (hi := (68402764210501850373 / 100000000000000000000))
    (y := (-((7167414305196164439 / 10000000000000000000)))) (u := (9766819180993555901 / 20000000000000000000))
  · norm_num [world12808, agent12808, scalar12808, tp12808, tm12808, ep12808, em12808, dsL]
  · norm_num [world12808, agent12808, scalar12808, tp12808, tm12808, ep12808, em12808, dsL]
  · norm_num [world12808, agent12808, scalar12808, tp12808, tm12808, ep12808, em12808, dsL]
  · norm_num [world12808, agent12808, scalar12808, tp12808, tm12808, ep12808, em12808, dsL]
  · norm_num [world12808, agent12808, scalar12808, tp12808, tm12808, ep12808, em12808, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12808, agent12808, tp12808, tm12808, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12808, agent12808, tp12808, tm12808, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12808, agent12808, scalar12808, tp12808, tm12808, ep12808, em12808, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12808, agent12808, tp12808, tm12808, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12808, agent12808, scalar12808, tp12808, tm12808, ep12808, em12808, dsL]

theorem tails12808 :
    exp (-((12808:ℝ)*ep12808)) ≤ scalar12808.upperTail ∧
    exp (-((12808:ℝ)*em12808)) ≤ scalar12808.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12808:ℝ)) (by norm_num [ep12808]) ?_)
      (show bp12808^8 ≤ scalar12808.upperTail by norm_num [bp12808, scalar12808])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12808, bp12808, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12808:ℝ)) (by norm_num [em12808]) ?_)
      (show bm12808^8 ≤ scalar12808.lowerTail by norm_num [bm12808, scalar12808])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12808, bm12808, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12808 :
    agent12808.root+dsL+scalar12808.worldRadius < √(1/100/aL) ∧
    2*(agent12808.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12808, agent12808, scalar12808, tp12808, tm12808, ep12808, em12808, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12808, agent12808, scalar12808, tp12808, tm12808, ep12808, em12808, dsL]

noncomputable def master12808 : MasterCertificate 12808 world12808 agent12808 :=
  master scalar12808 dsL tp12808 tm12808 ep12808 em12808
    (by norm_num [dsL]) (by norm_num [tp12808]) (by norm_num [tm12808])
    (by norm_num [ep12808]) (by norm_num [em12808])
    positive12808 negative12808 tails12808.1 tails12808.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12808.1 tailGuards12808.2

theorem preserves12808 : master12808.toScalarCertificate = scalar12808 := rfl

noncomputable def tp12809 : ℝ := (2326322973 / 10000000000)
noncomputable def tm12809 : ℝ := (-((95072097 / 156250000)))
noncomputable def ep12809 : ℝ := (51717537813847517 / 100000000000000000000)
noncomputable def em12809 : ℝ := (25181891394516179 / 50000000000000000000)
noncomputable def bp12809 : ℝ := (43689498253935599173 / 100000000000000000000)
noncomputable def bm12809 : ℝ := (44646819313586396661 / 100000000000000000000)

theorem positive12809 :
    Eplus aL (agent12809.root+dsL) scalar12809.worldRadius world12809.frame
      agent12809.frame tp12809 ≤ -ep12809 := by
  apply positive_check (eT := (115626270349774151343 / 100000000000000000000)) (y := (37938478728223865223 / 100000000000000000000)) (u := (73069262501435188087 / 50000000000000000000))
  · norm_num [world12809, agent12809, scalar12809, tp12809, tm12809, ep12809, em12809, dsL]
  · norm_num [world12809, agent12809, scalar12809, tp12809, tm12809, ep12809, em12809, dsL]
  · norm_num [world12809, agent12809, scalar12809, tp12809, tm12809, ep12809, em12809, dsL]
  · norm_num [world12809, agent12809, scalar12809, tp12809, tm12809, ep12809, em12809, dsL]
  · norm_num [world12809, agent12809, scalar12809, tp12809, tm12809, ep12809, em12809, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12809, agent12809, tp12809, tm12809, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12809, agent12809, scalar12809, tp12809, tm12809, ep12809, em12809, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12809, agent12809, tp12809, tm12809, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12809, agent12809, scalar12809, tp12809, tm12809, ep12809, em12809, dsL]

theorem negative12809 :
    Eminus aL (agent12809.root+dsL) scalar12809.worldRadius world12809.frame
      agent12809.frame tm12809 ≤ -em12809 := by
  apply negative_check (lo := (6840258621090752951 / 10000000000000000000)) (hi := (68402586210907529511 / 100000000000000000000))
    (y := (-((71674172266824722587 / 100000000000000000000)))) (u := (763032525596181397 / 1562500000000000000))
  · norm_num [world12809, agent12809, scalar12809, tp12809, tm12809, ep12809, em12809, dsL]
  · norm_num [world12809, agent12809, scalar12809, tp12809, tm12809, ep12809, em12809, dsL]
  · norm_num [world12809, agent12809, scalar12809, tp12809, tm12809, ep12809, em12809, dsL]
  · norm_num [world12809, agent12809, scalar12809, tp12809, tm12809, ep12809, em12809, dsL]
  · norm_num [world12809, agent12809, scalar12809, tp12809, tm12809, ep12809, em12809, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12809, agent12809, tp12809, tm12809, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12809, agent12809, tp12809, tm12809, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12809, agent12809, scalar12809, tp12809, tm12809, ep12809, em12809, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12809, agent12809, tp12809, tm12809, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12809, agent12809, scalar12809, tp12809, tm12809, ep12809, em12809, dsL]

theorem tails12809 :
    exp (-((12809:ℝ)*ep12809)) ≤ scalar12809.upperTail ∧
    exp (-((12809:ℝ)*em12809)) ≤ scalar12809.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12809:ℝ)) (by norm_num [ep12809]) ?_)
      (show bp12809^8 ≤ scalar12809.upperTail by norm_num [bp12809, scalar12809])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12809, bp12809, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12809:ℝ)) (by norm_num [em12809]) ?_)
      (show bm12809^8 ≤ scalar12809.lowerTail by norm_num [bm12809, scalar12809])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12809, bm12809, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12809 :
    agent12809.root+dsL+scalar12809.worldRadius < √(1/100/aL) ∧
    2*(agent12809.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12809, agent12809, scalar12809, tp12809, tm12809, ep12809, em12809, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12809, agent12809, scalar12809, tp12809, tm12809, ep12809, em12809, dsL]

noncomputable def master12809 : MasterCertificate 12809 world12809 agent12809 :=
  master scalar12809 dsL tp12809 tm12809 ep12809 em12809
    (by norm_num [dsL]) (by norm_num [tp12809]) (by norm_num [tm12809])
    (by norm_num [ep12809]) (by norm_num [em12809])
    positive12809 negative12809 tails12809.1 tails12809.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12809.1 tailGuards12809.2

theorem preserves12809 : master12809.toScalarCertificate = scalar12809 := rfl

noncomputable def tp12810 : ℝ := (465295583 / 2000000000)
noncomputable def tm12810 : ℝ := (-((380313153 / 625000000)))
noncomputable def ep12810 : ℝ := (10344285261567307 / 20000000000000000000)
noncomputable def em12810 : ℝ := (50367436265116663 / 100000000000000000000)
noncomputable def bp12810 : ℝ := (43683953908965011467 / 100000000000000000000)
noncomputable def bm12810 : ℝ := (1395043656817308519 / 3125000000000000000)

theorem positive12810 :
    Eplus aL (agent12810.root+dsL) scalar12810.worldRadius world12810.frame
      agent12810.frame tp12810 ≤ -ep12810 := by
  apply positive_check (eT := (903336113831508929 / 781250000000000000)) (y := (2371156939123594581 / 6250000000000000000)) (u := (18267321525292348589 / 12500000000000000000))
  · norm_num [world12810, agent12810, scalar12810, tp12810, tm12810, ep12810, em12810, dsL]
  · norm_num [world12810, agent12810, scalar12810, tp12810, tm12810, ep12810, em12810, dsL]
  · norm_num [world12810, agent12810, scalar12810, tp12810, tm12810, ep12810, em12810, dsL]
  · norm_num [world12810, agent12810, scalar12810, tp12810, tm12810, ep12810, em12810, dsL]
  · norm_num [world12810, agent12810, scalar12810, tp12810, tm12810, ep12810, em12810, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12810, agent12810, tp12810, tm12810, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12810, agent12810, scalar12810, tp12810, tm12810, ep12810, em12810, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12810, agent12810, tp12810, tm12810, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12810, agent12810, scalar12810, tp12810, tm12810, ep12810, em12810, dsL]

theorem negative12810 :
    Eminus aL (agent12810.root+dsL) scalar12810.worldRadius world12810.frame
      agent12810.frame tm12810 ≤ -em12810 := by
  apply negative_check (lo := (68401460802159788227 / 100000000000000000000)) (hi := (17100365200539947057 / 25000000000000000000))
    (y := (-((14334461234382206297 / 20000000000000000000)))) (u := (6104374117121503847 / 12500000000000000000))
  · norm_num [world12810, agent12810, scalar12810, tp12810, tm12810, ep12810, em12810, dsL]
  · norm_num [world12810, agent12810, scalar12810, tp12810, tm12810, ep12810, em12810, dsL]
  · norm_num [world12810, agent12810, scalar12810, tp12810, tm12810, ep12810, em12810, dsL]
  · norm_num [world12810, agent12810, scalar12810, tp12810, tm12810, ep12810, em12810, dsL]
  · norm_num [world12810, agent12810, scalar12810, tp12810, tm12810, ep12810, em12810, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12810, agent12810, tp12810, tm12810, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12810, agent12810, tp12810, tm12810, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12810, agent12810, scalar12810, tp12810, tm12810, ep12810, em12810, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12810, agent12810, tp12810, tm12810, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12810, agent12810, scalar12810, tp12810, tm12810, ep12810, em12810, dsL]

theorem tails12810 :
    exp (-((12810:ℝ)*ep12810)) ≤ scalar12810.upperTail ∧
    exp (-((12810:ℝ)*em12810)) ≤ scalar12810.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12810:ℝ)) (by norm_num [ep12810]) ?_)
      (show bp12810^8 ≤ scalar12810.upperTail by norm_num [bp12810, scalar12810])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12810, bp12810, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12810:ℝ)) (by norm_num [em12810]) ?_)
      (show bm12810^8 ≤ scalar12810.lowerTail by norm_num [bm12810, scalar12810])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12810, bm12810, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12810 :
    agent12810.root+dsL+scalar12810.worldRadius < √(1/100/aL) ∧
    2*(agent12810.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12810, agent12810, scalar12810, tp12810, tm12810, ep12810, em12810, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12810, agent12810, scalar12810, tp12810, tm12810, ep12810, em12810, dsL]

noncomputable def master12810 : MasterCertificate 12810 world12810 agent12810 :=
  master scalar12810 dsL tp12810 tm12810 ep12810 em12810
    (by norm_num [dsL]) (by norm_num [tp12810]) (by norm_num [tm12810])
    (by norm_num [ep12810]) (by norm_num [em12810])
    positive12810 negative12810 tails12810.1 tails12810.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12810.1 tailGuards12810.2

theorem preserves12810 : master12810.toScalarCertificate = scalar12810 := rfl

noncomputable def tp12811 : ℝ := (46531187 / 200000000)
noncomputable def tm12811 : ℝ := (-((6085184631 / 10000000000)))
noncomputable def ep12811 : ℝ := (12930978675424619 / 25000000000000000000)
noncomputable def em12811 : ℝ := (50369563814118479 / 100000000000000000000)
noncomputable def bp12811 : ℝ := (43679389161185253859 / 100000000000000000000)
noncomputable def bm12811 : ℝ := (44637065703305598723 / 100000000000000000000)

theorem positive12811 :
    Eplus aL (agent12811.root+dsL) scalar12811.worldRadius world12811.frame
      agent12811.frame tp12811 ≤ -ep12811 := by
  apply positive_check (eT := (14453405544091500323 / 12500000000000000000)) (y := (9484815939953645583 / 25000000000000000000)) (u := (9133729515060058847 / 6250000000000000000))
  · norm_num [world12811, agent12811, scalar12811, tp12811, tm12811, ep12811, em12811, dsL]
  · norm_num [world12811, agent12811, scalar12811, tp12811, tm12811, ep12811, em12811, dsL]
  · norm_num [world12811, agent12811, scalar12811, tp12811, tm12811, ep12811, em12811, dsL]
  · norm_num [world12811, agent12811, scalar12811, tp12811, tm12811, ep12811, em12811, dsL]
  · norm_num [world12811, agent12811, scalar12811, tp12811, tm12811, ep12811, em12811, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12811, agent12811, tp12811, tm12811, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12811, agent12811, scalar12811, tp12811, tm12811, ep12811, em12811, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12811, agent12811, tp12811, tm12811, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12811, agent12811, scalar12811, tp12811, tm12811, ep12811, em12811, dsL]

theorem negative12811 :
    Eminus aL (agent12811.root+dsL) scalar12811.worldRadius world12811.frame
      agent12811.frame tm12811 ≤ -em12811 := by
  apply negative_check (lo := (8550160417403015429 / 12500000000000000000)) (hi := (68401283339224123433 / 100000000000000000000))
    (y := (-((35836167535713126759 / 50000000000000000000)))) (u := (24417489411948926291 / 50000000000000000000))
  · norm_num [world12811, agent12811, scalar12811, tp12811, tm12811, ep12811, em12811, dsL]
  · norm_num [world12811, agent12811, scalar12811, tp12811, tm12811, ep12811, em12811, dsL]
  · norm_num [world12811, agent12811, scalar12811, tp12811, tm12811, ep12811, em12811, dsL]
  · norm_num [world12811, agent12811, scalar12811, tp12811, tm12811, ep12811, em12811, dsL]
  · norm_num [world12811, agent12811, scalar12811, tp12811, tm12811, ep12811, em12811, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12811, agent12811, tp12811, tm12811, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12811, agent12811, tp12811, tm12811, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12811, agent12811, scalar12811, tp12811, tm12811, ep12811, em12811, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12811, agent12811, tp12811, tm12811, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12811, agent12811, scalar12811, tp12811, tm12811, ep12811, em12811, dsL]

theorem tails12811 :
    exp (-((12811:ℝ)*ep12811)) ≤ scalar12811.upperTail ∧
    exp (-((12811:ℝ)*em12811)) ≤ scalar12811.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12811:ℝ)) (by norm_num [ep12811]) ?_)
      (show bp12811^8 ≤ scalar12811.upperTail by norm_num [bp12811, scalar12811])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12811, bp12811, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12811:ℝ)) (by norm_num [em12811]) ?_)
      (show bm12811^8 ≤ scalar12811.lowerTail by norm_num [bm12811, scalar12811])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12811, bm12811, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12811 :
    agent12811.root+dsL+scalar12811.worldRadius < √(1/100/aL) ∧
    2*(agent12811.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12811, agent12811, scalar12811, tp12811, tm12811, ep12811, em12811, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12811, agent12811, scalar12811, tp12811, tm12811, ep12811, em12811, dsL]

noncomputable def master12811 : MasterCertificate 12811 world12811 agent12811 :=
  master scalar12811 dsL tp12811 tm12811 ep12811 em12811
    (by norm_num [dsL]) (by norm_num [tp12811]) (by norm_num [tm12811])
    (by norm_num [ep12811]) (by norm_num [em12811])
    positive12811 negative12811 tails12811.1 tails12811.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12811.1 tailGuards12811.2

theorem preserves12811 : master12811.toScalarCertificate = scalar12811 := rfl

noncomputable def tp12812 : ℝ := (1163320381 / 5000000000)
noncomputable def tm12812 : ℝ := (-((3042679307 / 5000000000)))
noncomputable def ep12812 : ℝ := (2586320134899361 / 5000000000000000000)
noncomputable def em12812 : ℝ := (10074338196065953 / 20000000000000000000)
noncomputable def bp12812 : ℝ := (43674824896781165521 / 100000000000000000000)
noncomputable def bm12812 : ℝ := (22316367422460894099 / 50000000000000000000)

theorem positive12812 :
    Eplus aL (agent12812.root+dsL) scalar12812.worldRadius world12812.frame
      agent12812.frame tp12812 ≤ -ep12812 := by
  apply positive_check (eT := (23125493200390341361 / 20000000000000000000)) (y := (18970008171027381583 / 50000000000000000000)) (u := (14614077206631862547 / 10000000000000000000))
  · norm_num [world12812, agent12812, scalar12812, tp12812, tm12812, ep12812, em12812, dsL]
  · norm_num [world12812, agent12812, scalar12812, tp12812, tm12812, ep12812, em12812, dsL]
  · norm_num [world12812, agent12812, scalar12812, tp12812, tm12812, ep12812, em12812, dsL]
  · norm_num [world12812, agent12812, scalar12812, tp12812, tm12812, ep12812, em12812, dsL]
  · norm_num [world12812, agent12812, scalar12812, tp12812, tm12812, ep12812, em12812, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12812, agent12812, tp12812, tm12812, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12812, agent12812, scalar12812, tp12812, tm12812, ep12812, em12812, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12812, agent12812, tp12812, tm12812, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12812, agent12812, scalar12812, tp12812, tm12812, ep12812, em12812, dsL]

theorem negative12812 :
    Eminus aL (agent12812.root+dsL) scalar12812.worldRadius world12812.frame
      agent12812.frame tm12812 ≤ -em12812 := by
  apply negative_check (lo := (8550138334132560989 / 12500000000000000000)) (hi := (68401106673060487913 / 100000000000000000000))
    (y := (-((35836181346142471567 / 50000000000000000000)))) (u := (6104370666907402921 / 12500000000000000000))
  · norm_num [world12812, agent12812, scalar12812, tp12812, tm12812, ep12812, em12812, dsL]
  · norm_num [world12812, agent12812, scalar12812, tp12812, tm12812, ep12812, em12812, dsL]
  · norm_num [world12812, agent12812, scalar12812, tp12812, tm12812, ep12812, em12812, dsL]
  · norm_num [world12812, agent12812, scalar12812, tp12812, tm12812, ep12812, em12812, dsL]
  · norm_num [world12812, agent12812, scalar12812, tp12812, tm12812, ep12812, em12812, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12812, agent12812, tp12812, tm12812, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12812, agent12812, tp12812, tm12812, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12812, agent12812, scalar12812, tp12812, tm12812, ep12812, em12812, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12812, agent12812, tp12812, tm12812, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12812, agent12812, scalar12812, tp12812, tm12812, ep12812, em12812, dsL]

theorem tails12812 :
    exp (-((12812:ℝ)*ep12812)) ≤ scalar12812.upperTail ∧
    exp (-((12812:ℝ)*em12812)) ≤ scalar12812.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12812:ℝ)) (by norm_num [ep12812]) ?_)
      (show bp12812^8 ≤ scalar12812.upperTail by norm_num [bp12812, scalar12812])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12812, bp12812, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12812:ℝ)) (by norm_num [em12812]) ?_)
      (show bm12812^8 ≤ scalar12812.lowerTail by norm_num [bm12812, scalar12812])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12812, bm12812, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12812 :
    agent12812.root+dsL+scalar12812.worldRadius < √(1/100/aL) ∧
    2*(agent12812.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12812, agent12812, scalar12812, tp12812, tm12812, ep12812, em12812, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12812, agent12812, scalar12812, tp12812, tm12812, ep12812, em12812, dsL]

noncomputable def master12812 : MasterCertificate 12812 world12812 agent12812 :=
  master scalar12812 dsL tp12812 tm12812 ep12812 em12812
    (by norm_num [dsL]) (by norm_num [tp12812]) (by norm_num [tm12812])
    (by norm_num [ep12812]) (by norm_num [em12812])
    positive12812 negative12812 tails12812.1 tails12812.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12812.1 tailGuards12812.2

theorem preserves12812 : master12812.toScalarCertificate = scalar12812 := rfl

noncomputable def tp12813 : ℝ := (290840271 / 1250000000)
noncomputable def tm12813 : ℝ := (-((6085532521 / 10000000000)))
noncomputable def ep12813 : ℝ := (10345777780494717 / 20000000000000000000)
noncomputable def em12813 : ℝ := (787090882476811 / 1562500000000000000)
noncomputable def bp12813 : ℝ := (4367026209093706321 / 10000000000000000000)
noncomputable def bm12813 : ℝ := (44628405361674787941 / 100000000000000000000)

theorem positive12813 :
    Eplus aL (agent12813.root+dsL) scalar12813.worldRadius world12813.frame
      agent12813.frame tp12813 ≤ -ep12813 := by
  apply positive_check (eT := (115627687640781316579 / 100000000000000000000)) (y := (18970384659710938203 / 50000000000000000000)) (u := (14614187247739932739 / 10000000000000000000))
  · norm_num [world12813, agent12813, scalar12813, tp12813, tm12813, ep12813, em12813, dsL]
  · norm_num [world12813, agent12813, scalar12813, tp12813, tm12813, ep12813, em12813, dsL]
  · norm_num [world12813, agent12813, scalar12813, tp12813, tm12813, ep12813, em12813, dsL]
  · norm_num [world12813, agent12813, scalar12813, tp12813, tm12813, ep12813, em12813, dsL]
  · norm_num [world12813, agent12813, scalar12813, tp12813, tm12813, ep12813, em12813, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12813, agent12813, tp12813, tm12813, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12813, agent12813, scalar12813, tp12813, tm12813, ep12813, em12813, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12813, agent12813, tp12813, tm12813, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12813, agent12813, scalar12813, tp12813, tm12813, ep12813, em12813, dsL]

theorem negative12813 :
    Eminus aL (agent12813.root+dsL) scalar12813.worldRadius world12813.frame
      agent12813.frame tm12813 ≤ -em12813 := by
  apply negative_check (lo := (68400930274275297163 / 100000000000000000000)) (hi := (17100232568568824291 / 25000000000000000000))
    (y := (-((17918097565609633401 / 25000000000000000000)))) (u := (4883495187138613059 / 10000000000000000000))
  · norm_num [world12813, agent12813, scalar12813, tp12813, tm12813, ep12813, em12813, dsL]
  · norm_num [world12813, agent12813, scalar12813, tp12813, tm12813, ep12813, em12813, dsL]
  · norm_num [world12813, agent12813, scalar12813, tp12813, tm12813, ep12813, em12813, dsL]
  · norm_num [world12813, agent12813, scalar12813, tp12813, tm12813, ep12813, em12813, dsL]
  · norm_num [world12813, agent12813, scalar12813, tp12813, tm12813, ep12813, em12813, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12813, agent12813, tp12813, tm12813, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12813, agent12813, tp12813, tm12813, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12813, agent12813, scalar12813, tp12813, tm12813, ep12813, em12813, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12813, agent12813, tp12813, tm12813, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12813, agent12813, scalar12813, tp12813, tm12813, ep12813, em12813, dsL]

theorem tails12813 :
    exp (-((12813:ℝ)*ep12813)) ≤ scalar12813.upperTail ∧
    exp (-((12813:ℝ)*em12813)) ≤ scalar12813.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12813:ℝ)) (by norm_num [ep12813]) ?_)
      (show bp12813^8 ≤ scalar12813.upperTail by norm_num [bp12813, scalar12813])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12813, bp12813, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12813:ℝ)) (by norm_num [em12813]) ?_)
      (show bm12813^8 ≤ scalar12813.lowerTail by norm_num [bm12813, scalar12813])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12813, bm12813, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12813 :
    agent12813.root+dsL+scalar12813.worldRadius < √(1/100/aL) ∧
    2*(agent12813.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12813, agent12813, scalar12813, tp12813, tm12813, ep12813, em12813, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12813, agent12813, scalar12813, tp12813, tm12813, ep12813, em12813, dsL]

noncomputable def master12813 : MasterCertificate 12813 world12813 agent12813 :=
  master scalar12813 dsL tp12813 tm12813 ep12813 em12813
    (by norm_num [dsL]) (by norm_num [tp12813]) (by norm_num [tm12813])
    (by norm_num [ep12813]) (by norm_num [em12813])
    positive12813 negative12813 tails12813.1 tails12813.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12813.1 tailGuards12813.2

theorem preserves12813 : master12813.toScalarCertificate = scalar12813 := rfl

noncomputable def tp12814 : ℝ := (2326803543 / 10000000000)
noncomputable def tm12814 : ℝ := (-((6085706393 / 10000000000)))
noncomputable def ep12814 : ℝ := (10346274755903671 / 20000000000000000000)
noncomputable def em12814 : ℝ := (6296992592411331 / 12500000000000000000)
noncomputable def bp12814 : ℝ := (43665700418807790143 / 100000000000000000000)
noncomputable def bm12814 : ℝ := (44624076945736926333 / 100000000000000000000)

theorem positive12814 :
    Eplus aL (agent12814.root+dsL) scalar12814.worldRadius world12814.frame
      agent12814.frame tp12814 ≤ -ep12814 := by
  apply positive_check (eT := (57813954544402540631 / 50000000000000000000)) (y := (37941522204701657137 / 100000000000000000000)) (u := (3653574319054668539 / 2500000000000000000))
  · norm_num [world12814, agent12814, scalar12814, tp12814, tm12814, ep12814, em12814, dsL]
  · norm_num [world12814, agent12814, scalar12814, tp12814, tm12814, ep12814, em12814, dsL]
  · norm_num [world12814, agent12814, scalar12814, tp12814, tm12814, ep12814, em12814, dsL]
  · norm_num [world12814, agent12814, scalar12814, tp12814, tm12814, ep12814, em12814, dsL]
  · norm_num [world12814, agent12814, scalar12814, tp12814, tm12814, ep12814, em12814, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12814, agent12814, tp12814, tm12814, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12814, agent12814, scalar12814, tp12814, tm12814, ep12814, em12814, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12814, agent12814, tp12814, tm12814, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12814, agent12814, scalar12814, tp12814, tm12814, ep12814, em12814, dsL]

theorem negative12814 :
    Eminus aL (agent12814.root+dsL) scalar12814.worldRadius world12814.frame
      agent12814.frame tm12814 ≤ -em12814 := by
  apply negative_check (lo := (68400753967865081969 / 100000000000000000000)) (hi := (6840075396786508197 / 10000000000000000000))
    (y := (-((35836209153289811399 / 50000000000000000000)))) (u := (48834938176045247309 / 100000000000000000000))
  · norm_num [world12814, agent12814, scalar12814, tp12814, tm12814, ep12814, em12814, dsL]
  · norm_num [world12814, agent12814, scalar12814, tp12814, tm12814, ep12814, em12814, dsL]
  · norm_num [world12814, agent12814, scalar12814, tp12814, tm12814, ep12814, em12814, dsL]
  · norm_num [world12814, agent12814, scalar12814, tp12814, tm12814, ep12814, em12814, dsL]
  · norm_num [world12814, agent12814, scalar12814, tp12814, tm12814, ep12814, em12814, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12814, agent12814, tp12814, tm12814, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12814, agent12814, tp12814, tm12814, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12814, agent12814, scalar12814, tp12814, tm12814, ep12814, em12814, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12814, agent12814, tp12814, tm12814, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12814, agent12814, scalar12814, tp12814, tm12814, ep12814, em12814, dsL]

theorem tails12814 :
    exp (-((12814:ℝ)*ep12814)) ≤ scalar12814.upperTail ∧
    exp (-((12814:ℝ)*em12814)) ≤ scalar12814.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12814:ℝ)) (by norm_num [ep12814]) ?_)
      (show bp12814^8 ≤ scalar12814.upperTail by norm_num [bp12814, scalar12814])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12814, bp12814, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12814:ℝ)) (by norm_num [em12814]) ?_)
      (show bm12814^8 ≤ scalar12814.lowerTail by norm_num [bm12814, scalar12814])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12814, bm12814, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12814 :
    agent12814.root+dsL+scalar12814.worldRadius < √(1/100/aL) ∧
    2*(agent12814.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12814, agent12814, scalar12814, tp12814, tm12814, ep12814, em12814, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12814, agent12814, scalar12814, tp12814, tm12814, ep12814, em12814, dsL]

noncomputable def master12814 : MasterCertificate 12814 world12814 agent12814 :=
  master scalar12814 dsL tp12814 tm12814 ep12814 em12814
    (by norm_num [dsL]) (by norm_num [tp12814]) (by norm_num [tm12814])
    (by norm_num [ep12814]) (by norm_num [em12814])
    positive12814 negative12814 tails12814.1 tails12814.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12814.1 tailGuards12814.2

theorem preserves12814 : master12814.toScalarCertificate = scalar12814 := rfl

noncomputable def tp12815 : ℝ := (2326884797 / 10000000000)
noncomputable def tm12815 : ℝ := (-((3042940077 / 5000000000)))
noncomputable def ep12815 : ℝ := (646673218572387 / 1250000000000000000)
noncomputable def em12815 : ℝ := (50378063923608187 / 100000000000000000000)
noncomputable def bp12815 : ℝ := (10915284942695220451 / 25000000000000000000)
noncomputable def bm12815 : ℝ := (697183585656933343 / 1562500000000000000)

theorem positive12815 :
    Eplus aL (agent12815.root+dsL) scalar12815.worldRadius world12815.frame
      agent12815.frame tp12815 ≤ -ep12815 := by
  apply positive_check (eT := (28907032424155939213 / 25000000000000000000)) (y := (37942273269250856337 / 100000000000000000000)) (u := (1169152563154946097 / 800000000000000000))
  · norm_num [world12815, agent12815, scalar12815, tp12815, tm12815, ep12815, em12815, dsL]
  · norm_num [world12815, agent12815, scalar12815, tp12815, tm12815, ep12815, em12815, dsL]
  · norm_num [world12815, agent12815, scalar12815, tp12815, tm12815, ep12815, em12815, dsL]
  · norm_num [world12815, agent12815, scalar12815, tp12815, tm12815, ep12815, em12815, dsL]
  · norm_num [world12815, agent12815, scalar12815, tp12815, tm12815, ep12815, em12815, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12815, agent12815, tp12815, tm12815, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12815, agent12815, scalar12815, tp12815, tm12815, ep12815, em12815, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12815, agent12815, tp12815, tm12815, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12815, agent12815, scalar12815, tp12815, tm12815, ep12815, em12815, dsL]

theorem negative12815 :
    Eminus aL (agent12815.root+dsL) scalar12815.worldRadius world12815.frame
      agent12815.frame tm12815 ≤ -em12815 := by
  apply negative_check (lo := (13680115615644036641 / 20000000000000000000)) (hi := (34200289039110091603 / 50000000000000000000))
    (y := (-((35836222900909063551 / 50000000000000000000)))) (u := (48834924748764368307 / 100000000000000000000))
  · norm_num [world12815, agent12815, scalar12815, tp12815, tm12815, ep12815, em12815, dsL]
  · norm_num [world12815, agent12815, scalar12815, tp12815, tm12815, ep12815, em12815, dsL]
  · norm_num [world12815, agent12815, scalar12815, tp12815, tm12815, ep12815, em12815, dsL]
  · norm_num [world12815, agent12815, scalar12815, tp12815, tm12815, ep12815, em12815, dsL]
  · norm_num [world12815, agent12815, scalar12815, tp12815, tm12815, ep12815, em12815, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12815, agent12815, tp12815, tm12815, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12815, agent12815, tp12815, tm12815, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12815, agent12815, scalar12815, tp12815, tm12815, ep12815, em12815, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12815, agent12815, tp12815, tm12815, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12815, agent12815, scalar12815, tp12815, tm12815, ep12815, em12815, dsL]

theorem tails12815 :
    exp (-((12815:ℝ)*ep12815)) ≤ scalar12815.upperTail ∧
    exp (-((12815:ℝ)*em12815)) ≤ scalar12815.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12815:ℝ)) (by norm_num [ep12815]) ?_)
      (show bp12815^8 ≤ scalar12815.upperTail by norm_num [bp12815, scalar12815])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12815, bp12815, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12815:ℝ)) (by norm_num [em12815]) ?_)
      (show bm12815^8 ≤ scalar12815.lowerTail by norm_num [bm12815, scalar12815])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12815, bm12815, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12815 :
    agent12815.root+dsL+scalar12815.worldRadius < √(1/100/aL) ∧
    2*(agent12815.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12815, agent12815, scalar12815, tp12815, tm12815, ep12815, em12815, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12815, agent12815, scalar12815, tp12815, tm12815, ep12815, em12815, dsL]

noncomputable def master12815 : MasterCertificate 12815 world12815 agent12815 :=
  master scalar12815 dsL tp12815 tm12815 ep12815 em12815
    (by norm_num [dsL]) (by norm_num [tp12815]) (by norm_num [tm12815])
    (by norm_num [ep12815]) (by norm_num [em12815])
    positive12815 negative12815 tails12815.1 tails12815.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12815.1 tailGuards12815.2

theorem preserves12815 : master12815.toScalarCertificate = scalar12815 := rfl

noncomputable def tp12816 : ℝ := (2326966167 / 10000000000)
noncomputable def tm12816 : ℝ := (-((152151343 / 250000000)))
noncomputable def ep12816 : ℝ := (51736340181500251 / 100000000000000000000)
noncomputable def em12816 : ℝ := (6297523275363181 / 12500000000000000000)
noncomputable def bp12816 : ℝ := (1746263201391201581 / 4000000000000000000)
noncomputable def bm12816 : ℝ := (44615422848047022119 / 100000000000000000000)

theorem positive12816 :
    Eplus aL (agent12816.root+dsL) scalar12816.worldRadius world12816.frame
      agent12816.frame tp12816 ≤ -ep12816 := by
  apply positive_check (eT := (5781417558718554943 / 5000000000000000000)) (y := (37943026614734330627 / 100000000000000000000)) (u := (146145171368269006957 / 100000000000000000000))
  · norm_num [world12816, agent12816, scalar12816, tp12816, tm12816, ep12816, em12816, dsL]
  · norm_num [world12816, agent12816, scalar12816, tp12816, tm12816, ep12816, em12816, dsL]
  · norm_num [world12816, agent12816, scalar12816, tp12816, tm12816, ep12816, em12816, dsL]
  · norm_num [world12816, agent12816, scalar12816, tp12816, tm12816, ep12816, em12816, dsL]
  · norm_num [world12816, agent12816, scalar12816, tp12816, tm12816, ep12816, em12816, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12816, agent12816, tp12816, tm12816, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12816, agent12816, scalar12816, tp12816, tm12816, ep12816, em12816, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12816, agent12816, tp12816, tm12816, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12816, agent12816, scalar12816, tp12816, tm12816, ep12816, em12816, dsL]

theorem negative12816 :
    Eminus aL (agent12816.root+dsL) scalar12816.worldRadius world12816.frame
      agent12816.frame tm12816 ≤ -em12816 := by
  apply negative_check (lo := (2736016118555536657 / 4000000000000000000)) (hi := (34200201481944208213 / 50000000000000000000))
    (y := (-((17918118014845699731 / 25000000000000000000)))) (u := (976698238518082069 / 2000000000000000000))
  · norm_num [world12816, agent12816, scalar12816, tp12816, tm12816, ep12816, em12816, dsL]
  · norm_num [world12816, agent12816, scalar12816, tp12816, tm12816, ep12816, em12816, dsL]
  · norm_num [world12816, agent12816, scalar12816, tp12816, tm12816, ep12816, em12816, dsL]
  · norm_num [world12816, agent12816, scalar12816, tp12816, tm12816, ep12816, em12816, dsL]
  · norm_num [world12816, agent12816, scalar12816, tp12816, tm12816, ep12816, em12816, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12816, agent12816, tp12816, tm12816, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12816, agent12816, tp12816, tm12816, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12816, agent12816, scalar12816, tp12816, tm12816, ep12816, em12816, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12816, agent12816, tp12816, tm12816, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12816, agent12816, scalar12816, tp12816, tm12816, ep12816, em12816, dsL]

theorem tails12816 :
    exp (-((12816:ℝ)*ep12816)) ≤ scalar12816.upperTail ∧
    exp (-((12816:ℝ)*em12816)) ≤ scalar12816.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12816:ℝ)) (by norm_num [ep12816]) ?_)
      (show bp12816^8 ≤ scalar12816.upperTail by norm_num [bp12816, scalar12816])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12816, bp12816, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12816:ℝ)) (by norm_num [em12816]) ?_)
      (show bm12816^8 ≤ scalar12816.lowerTail by norm_num [bm12816, scalar12816])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12816, bm12816, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12816 :
    agent12816.root+dsL+scalar12816.worldRadius < √(1/100/aL) ∧
    2*(agent12816.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12816, agent12816, scalar12816, tp12816, tm12816, ep12816, em12816, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12816, agent12816, scalar12816, tp12816, tm12816, ep12816, em12816, dsL]

noncomputable def master12816 : MasterCertificate 12816 world12816 agent12816 :=
  master scalar12816 dsL tp12816 tm12816 ep12816 em12816
    (by norm_num [dsL]) (by norm_num [tp12816]) (by norm_num [tm12816])
    (by norm_num [ep12816]) (by norm_num [em12816])
    positive12816 negative12816 tails12816.1 tails12816.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12816.1 tailGuards12816.2

theorem preserves12816 : master12816.toScalarCertificate = scalar12816 := rfl

noncomputable def tp12817 : ℝ := (465409469 / 2000000000)
noncomputable def tm12817 : ℝ := (-((6086227449 / 10000000000)))
noncomputable def ep12817 : ℝ := (51738821389770369 / 100000000000000000000)
noncomputable def em12817 : ℝ := (25191153536851523 / 50000000000000000000)
noncomputable def bp12817 : ℝ := (43652021544292308931 / 100000000000000000000)
noncomputable def bm12817 : ℝ := (22305548701793896231 / 50000000000000000000)

theorem positive12817 :
    Eplus aL (agent12817.root+dsL) scalar12817.worldRadius world12817.frame
      agent12817.frame tp12817 ≤ -ep12817 := by
  apply positive_check (eT := (115628571299609246797 / 100000000000000000000)) (y := (9485944274326657673 / 25000000000000000000)) (u := (146146268166426018243 / 100000000000000000000))
  · norm_num [world12817, agent12817, scalar12817, tp12817, tm12817, ep12817, em12817, dsL]
  · norm_num [world12817, agent12817, scalar12817, tp12817, tm12817, ep12817, em12817, dsL]
  · norm_num [world12817, agent12817, scalar12817, tp12817, tm12817, ep12817, em12817, dsL]
  · norm_num [world12817, agent12817, scalar12817, tp12817, tm12817, ep12817, em12817, dsL]
  · norm_num [world12817, agent12817, scalar12817, tp12817, tm12817, ep12817, em12817, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12817, agent12817, tp12817, tm12817, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12817, agent12817, scalar12817, tp12817, tm12817, ep12817, em12817, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12817, agent12817, tp12817, tm12817, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12817, agent12817, scalar12817, tp12817, tm12817, ep12817, em12817, dsL]

theorem negative12817 :
    Eminus aL (agent12817.root+dsL) scalar12817.worldRadius world12817.frame
      agent12817.frame tm12817 ≤ -em12817 := by
  apply negative_check (lo := (68400227096782917189 / 100000000000000000000)) (hi := (6840022709678291719 / 10000000000000000000))
    (y := (-((3583625029108923433 / 5000000000000000000)))) (u := (48834897996823945811 / 100000000000000000000))
  · norm_num [world12817, agent12817, scalar12817, tp12817, tm12817, ep12817, em12817, dsL]
  · norm_num [world12817, agent12817, scalar12817, tp12817, tm12817, ep12817, em12817, dsL]
  · norm_num [world12817, agent12817, scalar12817, tp12817, tm12817, ep12817, em12817, dsL]
  · norm_num [world12817, agent12817, scalar12817, tp12817, tm12817, ep12817, em12817, dsL]
  · norm_num [world12817, agent12817, scalar12817, tp12817, tm12817, ep12817, em12817, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12817, agent12817, tp12817, tm12817, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12817, agent12817, tp12817, tm12817, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12817, agent12817, scalar12817, tp12817, tm12817, ep12817, em12817, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12817, agent12817, tp12817, tm12817, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12817, agent12817, scalar12817, tp12817, tm12817, ep12817, em12817, dsL]

theorem tails12817 :
    exp (-((12817:ℝ)*ep12817)) ≤ scalar12817.upperTail ∧
    exp (-((12817:ℝ)*em12817)) ≤ scalar12817.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12817:ℝ)) (by norm_num [ep12817]) ?_)
      (show bp12817^8 ≤ scalar12817.upperTail by norm_num [bp12817, scalar12817])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12817, bp12817, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12817:ℝ)) (by norm_num [em12817]) ?_)
      (show bm12817^8 ≤ scalar12817.lowerTail by norm_num [bm12817, scalar12817])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12817, bm12817, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12817 :
    agent12817.root+dsL+scalar12817.worldRadius < √(1/100/aL) ∧
    2*(agent12817.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12817, agent12817, scalar12817, tp12817, tm12817, ep12817, em12817, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12817, agent12817, scalar12817, tp12817, tm12817, ep12817, em12817, dsL]

noncomputable def master12817 : MasterCertificate 12817 world12817 agent12817 :=
  master scalar12817 dsL tp12817 tm12817 ep12817 em12817
    (by norm_num [dsL]) (by norm_num [tp12817]) (by norm_num [tm12817])
    (by norm_num [ep12817]) (by norm_num [em12817])
    positive12817 negative12817 tails12817.1 tails12817.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12817.1 tailGuards12817.2

theorem preserves12817 : master12817.toScalarCertificate = scalar12817 := rfl

noncomputable def tp12818 : ℝ := (465425701 / 2000000000)
noncomputable def tm12818 : ℝ := (-((608640083 / 1000000000)))
noncomputable def ep12818 : ℝ := (51741300806218351 / 100000000000000000000)
noncomputable def em12818 : ℝ := (50384426276629181 / 100000000000000000000)
noncomputable def bp12818 : ℝ := (43647464512138067407 / 100000000000000000000)
noncomputable def bm12818 : ℝ := (8921354666802632473 / 20000000000000000000)

theorem positive12818 :
    Eplus aL (agent12818.root+dsL) scalar12818.worldRadius world12818.frame
      agent12818.frame tp12818 ≤ -ep12818 := by
  apply positive_check (eT := (2890719783198055887 / 2500000000000000000)) (y := (18972263882065075189 / 50000000000000000000)) (u := (146147365242092642093 / 100000000000000000000))
  · norm_num [world12818, agent12818, scalar12818, tp12818, tm12818, ep12818, em12818, dsL]
  · norm_num [world12818, agent12818, scalar12818, tp12818, tm12818, ep12818, em12818, dsL]
  · norm_num [world12818, agent12818, scalar12818, tp12818, tm12818, ep12818, em12818, dsL]
  · norm_num [world12818, agent12818, scalar12818, tp12818, tm12818, ep12818, em12818, dsL]
  · norm_num [world12818, agent12818, scalar12818, tp12818, tm12818, ep12818, em12818, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12818, agent12818, tp12818, tm12818, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12818, agent12818, scalar12818, tp12818, tm12818, ep12818, em12818, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12818, agent12818, tp12818, tm12818, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12818, agent12818, scalar12818, tp12818, tm12818, ep12818, em12818, dsL]

theorem negative12818 :
    Eminus aL (agent12818.root+dsL) scalar12818.worldRadius world12818.frame
      agent12818.frame tm12818 ≤ -em12818 := by
  apply negative_check (lo := (684000526579667769 / 1000000000000000000)) (hi := (68400052657966776901 / 100000000000000000000))
    (y := (-((7167252641962500169 / 10000000000000000000)))) (u := (24417442689567458233 / 50000000000000000000))
  · norm_num [world12818, agent12818, scalar12818, tp12818, tm12818, ep12818, em12818, dsL]
  · norm_num [world12818, agent12818, scalar12818, tp12818, tm12818, ep12818, em12818, dsL]
  · norm_num [world12818, agent12818, scalar12818, tp12818, tm12818, ep12818, em12818, dsL]
  · norm_num [world12818, agent12818, scalar12818, tp12818, tm12818, ep12818, em12818, dsL]
  · norm_num [world12818, agent12818, scalar12818, tp12818, tm12818, ep12818, em12818, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12818, agent12818, tp12818, tm12818, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12818, agent12818, tp12818, tm12818, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12818, agent12818, scalar12818, tp12818, tm12818, ep12818, em12818, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12818, agent12818, tp12818, tm12818, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12818, agent12818, scalar12818, tp12818, tm12818, ep12818, em12818, dsL]

theorem tails12818 :
    exp (-((12818:ℝ)*ep12818)) ≤ scalar12818.upperTail ∧
    exp (-((12818:ℝ)*em12818)) ≤ scalar12818.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12818:ℝ)) (by norm_num [ep12818]) ?_)
      (show bp12818^8 ≤ scalar12818.upperTail by norm_num [bp12818, scalar12818])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12818, bp12818, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12818:ℝ)) (by norm_num [em12818]) ?_)
      (show bm12818^8 ≤ scalar12818.lowerTail by norm_num [bm12818, scalar12818])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12818, bm12818, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12818 :
    agent12818.root+dsL+scalar12818.worldRadius < √(1/100/aL) ∧
    2*(agent12818.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12818, agent12818, scalar12818, tp12818, tm12818, ep12818, em12818, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12818, agent12818, scalar12818, tp12818, tm12818, ep12818, em12818, dsL]

noncomputable def master12818 : MasterCertificate 12818 world12818 agent12818 :=
  master scalar12818 dsL tp12818 tm12818 ep12818 em12818
    (by norm_num [dsL]) (by norm_num [tp12818]) (by norm_num [tm12818])
    (by norm_num [ep12818]) (by norm_num [em12818])
    positive12818 negative12818 tails12818.1 tails12818.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12818.1 tailGuards12818.2

theorem preserves12818 : master12818.toScalarCertificate = scalar12818 := rfl

noncomputable def tp12819 : ℝ := (232720967 / 1000000000)
noncomputable def tm12819 : ℝ := (-((6086574237 / 10000000000)))
noncomputable def ep12819 : ℝ := (51743779521257371 / 100000000000000000000)
noncomputable def em12819 : ℝ := (50386544838120597 / 100000000000000000000)
noncomputable def bp12819 : ℝ := (43642908175702136501 / 100000000000000000000)
noncomputable def bm12819 : ℝ := (44602449905690774167 / 100000000000000000000)

theorem positive12819 :
    Eplus aL (agent12819.root+dsL) scalar12819.worldRadius world12819.frame
      agent12819.frame tp12819 ≤ -ep12819 := by
  apply positive_check (eT := (57814505712596372849 / 50000000000000000000)) (y := (3794527876784302629 / 10000000000000000000)) (u := (36537115704588323651 / 25000000000000000000))
  · norm_num [world12819, agent12819, scalar12819, tp12819, tm12819, ep12819, em12819, dsL]
  · norm_num [world12819, agent12819, scalar12819, tp12819, tm12819, ep12819, em12819, dsL]
  · norm_num [world12819, agent12819, scalar12819, tp12819, tm12819, ep12819, em12819, dsL]
  · norm_num [world12819, agent12819, scalar12819, tp12819, tm12819, ep12819, em12819, dsL]
  · norm_num [world12819, agent12819, scalar12819, tp12819, tm12819, ep12819, em12819, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12819, agent12819, tp12819, tm12819, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12819, agent12819, scalar12819, tp12819, tm12819, ep12819, em12819, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12819, agent12819, tp12819, tm12819, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12819, agent12819, scalar12819, tp12819, tm12819, ep12819, em12819, dsL]

theorem negative12819 :
    Eminus aL (agent12819.root+dsL) scalar12819.worldRadius world12819.frame
      agent12819.frame tm12819 ≤ -em12819 := by
  apply negative_check (lo := (17099969512793310259 / 25000000000000000000)) (hi := (68399878051173241037 / 100000000000000000000))
    (y := (-((17918138290345359527 / 25000000000000000000)))) (u := (24417436159915279259 / 50000000000000000000))
  · norm_num [world12819, agent12819, scalar12819, tp12819, tm12819, ep12819, em12819, dsL]
  · norm_num [world12819, agent12819, scalar12819, tp12819, tm12819, ep12819, em12819, dsL]
  · norm_num [world12819, agent12819, scalar12819, tp12819, tm12819, ep12819, em12819, dsL]
  · norm_num [world12819, agent12819, scalar12819, tp12819, tm12819, ep12819, em12819, dsL]
  · norm_num [world12819, agent12819, scalar12819, tp12819, tm12819, ep12819, em12819, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12819, agent12819, tp12819, tm12819, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12819, agent12819, tp12819, tm12819, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12819, agent12819, scalar12819, tp12819, tm12819, ep12819, em12819, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12819, agent12819, tp12819, tm12819, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12819, agent12819, scalar12819, tp12819, tm12819, ep12819, em12819, dsL]

theorem tails12819 :
    exp (-((12819:ℝ)*ep12819)) ≤ scalar12819.upperTail ∧
    exp (-((12819:ℝ)*em12819)) ≤ scalar12819.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12819:ℝ)) (by norm_num [ep12819]) ?_)
      (show bp12819^8 ≤ scalar12819.upperTail by norm_num [bp12819, scalar12819])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12819, bp12819, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12819:ℝ)) (by norm_num [em12819]) ?_)
      (show bm12819^8 ≤ scalar12819.lowerTail by norm_num [bm12819, scalar12819])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12819, bm12819, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12819 :
    agent12819.root+dsL+scalar12819.worldRadius < √(1/100/aL) ∧
    2*(agent12819.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12819, agent12819, scalar12819, tp12819, tm12819, ep12819, em12819, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12819, agent12819, scalar12819, tp12819, tm12819, ep12819, em12819, dsL]

noncomputable def master12819 : MasterCertificate 12819 world12819 agent12819 :=
  master scalar12819 dsL tp12819 tm12819 ep12819 em12819
    (by norm_num [dsL]) (by norm_num [tp12819]) (by norm_num [tm12819])
    (by norm_num [ep12819]) (by norm_num [em12819])
    positive12819 negative12819 tails12819.1 tails12819.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12819.1 tailGuards12819.2

theorem preserves12819 : master12819.toScalarCertificate = scalar12819 := rfl

noncomputable def tp12820 : ℝ := (581841043 / 2500000000)
noncomputable def tm12820 : ℝ := (-((1521742347 / 2500000000)))
noncomputable def ep12820 : ℝ := (10349530727152003 / 20000000000000000000)
noncomputable def em12820 : ℝ := (12597546187645559 / 25000000000000000000)
noncomputable def bp12820 : ℝ := (872747524922808239 / 2000000000000000000)
noncomputable def bm12820 : ℝ := (44597039386765339591 / 100000000000000000000)

theorem positive12820 :
    Eplus aL (agent12820.root+dsL) scalar12820.worldRadius world12820.frame
      agent12820.frame tp12820 ≤ -ep12820 := by
  apply positive_check (eT := (115629760686613961509 / 100000000000000000000)) (y := (37945308883354006167 / 100000000000000000000)) (u := (146148506831716289011 / 100000000000000000000))
  · norm_num [world12820, agent12820, scalar12820, tp12820, tm12820, ep12820, em12820, dsL]
  · norm_num [world12820, agent12820, scalar12820, tp12820, tm12820, ep12820, em12820, dsL]
  · norm_num [world12820, agent12820, scalar12820, tp12820, tm12820, ep12820, em12820, dsL]
  · norm_num [world12820, agent12820, scalar12820, tp12820, tm12820, ep12820, em12820, dsL]
  · norm_num [world12820, agent12820, scalar12820, tp12820, tm12820, ep12820, em12820, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12820, agent12820, tp12820, tm12820, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12820, agent12820, scalar12820, tp12820, tm12820, ep12820, em12820, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12820, agent12820, tp12820, tm12820, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12820, agent12820, scalar12820, tp12820, tm12820, ep12820, em12820, dsL]

theorem negative12820 :
    Eminus aL (agent12820.root+dsL) scalar12820.worldRadius world12820.frame
      agent12820.frame tm12820 ≤ -em12820 := by
  apply negative_check (lo := (68398756987364136269 / 100000000000000000000)) (hi := (6839875698736413627 / 10000000000000000000))
    (y := (-((35835343422731687071 / 50000000000000000000)))) (u := (12208945935332801387 / 25000000000000000000))
  · norm_num [world12820, agent12820, scalar12820, tp12820, tm12820, ep12820, em12820, dsL]
  · norm_num [world12820, agent12820, scalar12820, tp12820, tm12820, ep12820, em12820, dsL]
  · norm_num [world12820, agent12820, scalar12820, tp12820, tm12820, ep12820, em12820, dsL]
  · norm_num [world12820, agent12820, scalar12820, tp12820, tm12820, ep12820, em12820, dsL]
  · norm_num [world12820, agent12820, scalar12820, tp12820, tm12820, ep12820, em12820, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12820, agent12820, tp12820, tm12820, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12820, agent12820, tp12820, tm12820, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12820, agent12820, scalar12820, tp12820, tm12820, ep12820, em12820, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12820, agent12820, tp12820, tm12820, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12820, agent12820, scalar12820, tp12820, tm12820, ep12820, em12820, dsL]

theorem tails12820 :
    exp (-((12820:ℝ)*ep12820)) ≤ scalar12820.upperTail ∧
    exp (-((12820:ℝ)*em12820)) ≤ scalar12820.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12820:ℝ)) (by norm_num [ep12820]) ?_)
      (show bp12820^8 ≤ scalar12820.upperTail by norm_num [bp12820, scalar12820])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12820, bp12820, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12820:ℝ)) (by norm_num [em12820]) ?_)
      (show bm12820^8 ≤ scalar12820.lowerTail by norm_num [bm12820, scalar12820])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12820, bm12820, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12820 :
    agent12820.root+dsL+scalar12820.worldRadius < √(1/100/aL) ∧
    2*(agent12820.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12820, agent12820, scalar12820, tp12820, tm12820, ep12820, em12820, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12820, agent12820, scalar12820, tp12820, tm12820, ep12820, em12820, dsL]

noncomputable def master12820 : MasterCertificate 12820 world12820 agent12820 :=
  master scalar12820 dsL tp12820 tm12820 ep12820 em12820
    (by norm_num [dsL]) (by norm_num [tp12820]) (by norm_num [tm12820])
    (by norm_num [ep12820]) (by norm_num [em12820])
    positive12820 negative12820 tails12820.1 tails12820.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12820.1 tailGuards12820.2

theorem preserves12820 : master12820.toScalarCertificate = scalar12820 := rfl

noncomputable def tp12821 : ℝ := (145465329 / 625000000)
noncomputable def tm12821 : ℝ := (-((380446407 / 625000000)))
noncomputable def ep12821 : ℝ := (517501291717319 / 1000000000000000000)
noncomputable def em12821 : ℝ := (787379693655423 / 1562500000000000000)
noncomputable def bp12821 : ℝ := (43632822568968113419 / 100000000000000000000)
noncomputable def bm12821 : ℝ := (44592718430175050367 / 100000000000000000000)

theorem positive12821 :
    Eplus aL (agent12821.root+dsL) scalar12821.worldRadius world12821.frame
      agent12821.frame tp12821 ≤ -ep12821 := by
  apply positive_check (eT := (115629980312518788629 / 100000000000000000000)) (y := (1517842373104446297 / 4000000000000000000)) (u := (29229920719781605599 / 20000000000000000000))
  · norm_num [world12821, agent12821, scalar12821, tp12821, tm12821, ep12821, em12821, dsL]
  · norm_num [world12821, agent12821, scalar12821, tp12821, tm12821, ep12821, em12821, dsL]
  · norm_num [world12821, agent12821, scalar12821, tp12821, tm12821, ep12821, em12821, dsL]
  · norm_num [world12821, agent12821, scalar12821, tp12821, tm12821, ep12821, em12821, dsL]
  · norm_num [world12821, agent12821, scalar12821, tp12821, tm12821, ep12821, em12821, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12821, agent12821, tp12821, tm12821, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12821, agent12821, scalar12821, tp12821, tm12821, ep12821, em12821, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12821, agent12821, tp12821, tm12821, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12821, agent12821, scalar12821, tp12821, tm12821, ep12821, em12821, dsL]

theorem negative12821 :
    Eminus aL (agent12821.root+dsL) scalar12821.worldRadius world12821.frame
      agent12821.frame tm12821 ≤ -em12821 := by
  apply negative_check (lo := (34199291748639717897 / 50000000000000000000)) (hi := (13679716699455887159 / 20000000000000000000))
    (y := (-((8958838993867288317 / 12500000000000000000)))) (u := (6104471435109662419 / 12500000000000000000))
  · norm_num [world12821, agent12821, scalar12821, tp12821, tm12821, ep12821, em12821, dsL]
  · norm_num [world12821, agent12821, scalar12821, tp12821, tm12821, ep12821, em12821, dsL]
  · norm_num [world12821, agent12821, scalar12821, tp12821, tm12821, ep12821, em12821, dsL]
  · norm_num [world12821, agent12821, scalar12821, tp12821, tm12821, ep12821, em12821, dsL]
  · norm_num [world12821, agent12821, scalar12821, tp12821, tm12821, ep12821, em12821, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12821, agent12821, tp12821, tm12821, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12821, agent12821, tp12821, tm12821, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12821, agent12821, scalar12821, tp12821, tm12821, ep12821, em12821, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12821, agent12821, tp12821, tm12821, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12821, agent12821, scalar12821, tp12821, tm12821, ep12821, em12821, dsL]

theorem tails12821 :
    exp (-((12821:ℝ)*ep12821)) ≤ scalar12821.upperTail ∧
    exp (-((12821:ℝ)*em12821)) ≤ scalar12821.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12821:ℝ)) (by norm_num [ep12821]) ?_)
      (show bp12821^8 ≤ scalar12821.upperTail by norm_num [bp12821, scalar12821])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12821, bp12821, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12821:ℝ)) (by norm_num [em12821]) ?_)
      (show bm12821^8 ≤ scalar12821.lowerTail by norm_num [bm12821, scalar12821])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12821, bm12821, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12821 :
    agent12821.root+dsL+scalar12821.worldRadius < √(1/100/aL) ∧
    2*(agent12821.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12821, agent12821, scalar12821, tp12821, tm12821, ep12821, em12821, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12821, agent12821, scalar12821, tp12821, tm12821, ep12821, em12821, dsL]

noncomputable def master12821 : MasterCertificate 12821 world12821 agent12821 :=
  master scalar12821 dsL tp12821 tm12821 ep12821 em12821
    (by norm_num [dsL]) (by norm_num [tp12821]) (by norm_num [tm12821])
    (by norm_num [ep12821]) (by norm_num [em12821])
    positive12821 negative12821 tails12821.1 tails12821.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12821.1 tailGuards12821.2

theorem preserves12821 : master12821.toScalarCertificate = scalar12821 := rfl

noncomputable def tp12822 : ℝ := (581881563 / 2500000000)
noncomputable def tm12822 : ℝ := (-((6087315503 / 10000000000)))
noncomputable def ep12822 : ℝ := (51752604172812677 / 100000000000000000000)
noncomputable def em12822 : ℝ := (50394415510507907 / 100000000000000000000)
noncomputable def bp12822 : ℝ := (43628269470999581349 / 100000000000000000000)
noncomputable def bm12822 : ℝ := (44588398032879976273 / 100000000000000000000)

theorem positive12822 :
    Eplus aL (agent12822.root+dsL) scalar12822.worldRadius world12822.frame
      agent12822.frame tp12822 ≤ -ep12822 := by
  apply positive_check (eT := (5781509961050335131 / 5000000000000000000)) (y := (37946808351862291701 / 100000000000000000000)) (u := (5846027931959267993 / 4000000000000000000))
  · norm_num [world12822, agent12822, scalar12822, tp12822, tm12822, ep12822, em12822, dsL]
  · norm_num [world12822, agent12822, scalar12822, tp12822, tm12822, ep12822, em12822, dsL]
  · norm_num [world12822, agent12822, scalar12822, tp12822, tm12822, ep12822, em12822, dsL]
  · norm_num [world12822, agent12822, scalar12822, tp12822, tm12822, ep12822, em12822, dsL]
  · norm_num [world12822, agent12822, scalar12822, tp12822, tm12822, ep12822, em12822, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12822, agent12822, tp12822, tm12822, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12822, agent12822, scalar12822, tp12822, tm12822, ep12822, em12822, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12822, agent12822, tp12822, tm12822, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12822, agent12822, scalar12822, tp12822, tm12822, ep12822, em12822, dsL]

theorem negative12822 :
    Eminus aL (agent12822.root+dsL) scalar12822.worldRadius world12822.frame
      agent12822.frame tm12822 ≤ -em12822 := by
  apply negative_check (lo := (68398410517721230193 / 100000000000000000000)) (hi := (34199205258860615097 / 50000000000000000000))
    (y := (-((17917684177707887903 / 25000000000000000000)))) (u := (24417879694596956111 / 50000000000000000000))
  · norm_num [world12822, agent12822, scalar12822, tp12822, tm12822, ep12822, em12822, dsL]
  · norm_num [world12822, agent12822, scalar12822, tp12822, tm12822, ep12822, em12822, dsL]
  · norm_num [world12822, agent12822, scalar12822, tp12822, tm12822, ep12822, em12822, dsL]
  · norm_num [world12822, agent12822, scalar12822, tp12822, tm12822, ep12822, em12822, dsL]
  · norm_num [world12822, agent12822, scalar12822, tp12822, tm12822, ep12822, em12822, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12822, agent12822, tp12822, tm12822, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12822, agent12822, tp12822, tm12822, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12822, agent12822, scalar12822, tp12822, tm12822, ep12822, em12822, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12822, agent12822, tp12822, tm12822, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12822, agent12822, scalar12822, tp12822, tm12822, ep12822, em12822, dsL]

theorem tails12822 :
    exp (-((12822:ℝ)*ep12822)) ≤ scalar12822.upperTail ∧
    exp (-((12822:ℝ)*em12822)) ≤ scalar12822.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12822:ℝ)) (by norm_num [ep12822]) ?_)
      (show bp12822^8 ≤ scalar12822.upperTail by norm_num [bp12822, scalar12822])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12822, bp12822, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12822:ℝ)) (by norm_num [em12822]) ?_)
      (show bm12822^8 ≤ scalar12822.lowerTail by norm_num [bm12822, scalar12822])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12822, bm12822, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12822 :
    agent12822.root+dsL+scalar12822.worldRadius < √(1/100/aL) ∧
    2*(agent12822.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12822, agent12822, scalar12822, tp12822, tm12822, ep12822, em12822, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12822, agent12822, scalar12822, tp12822, tm12822, ep12822, em12822, dsL]

noncomputable def master12822 : MasterCertificate 12822 world12822 agent12822 :=
  master scalar12822 dsL tp12822 tm12822 ep12822 em12822
    (by norm_num [dsL]) (by norm_num [tp12822]) (by norm_num [tm12822])
    (by norm_num [ep12822]) (by norm_num [em12822])
    positive12822 negative12822 tails12822.1 tails12822.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12822.1 tailGuards12822.2

theorem preserves12822 : master12822.toScalarCertificate = scalar12822 := rfl

noncomputable def tp12823 : ℝ := (1163803629 / 5000000000)
noncomputable def tm12823 : ℝ := (-((3043744321 / 5000000000)))
noncomputable def ep12823 : ℝ := (3234692345591937 / 6250000000000000000)
noncomputable def em12823 : ℝ := (25198264556193781 / 50000000000000000000)
noncomputable def bp12823 : ℝ := (43623717728061837511 / 100000000000000000000)
noncomputable def bm12823 : ℝ := (11146019725212626373 / 25000000000000000000)

theorem positive12823 :
    Eplus aL (agent12823.root+dsL) scalar12823.worldRadius world12823.frame
      agent12823.frame tp12823 ≤ -ep12823 := by
  apply positive_check (eT := (115630418292289214437 / 100000000000000000000)) (y := (18973779019174847943 / 50000000000000000000)) (u := (73075896987562578507 / 50000000000000000000))
  · norm_num [world12823, agent12823, scalar12823, tp12823, tm12823, ep12823, em12823, dsL]
  · norm_num [world12823, agent12823, scalar12823, tp12823, tm12823, ep12823, em12823, dsL]
  · norm_num [world12823, agent12823, scalar12823, tp12823, tm12823, ep12823, em12823, dsL]
  · norm_num [world12823, agent12823, scalar12823, tp12823, tm12823, ep12823, em12823, dsL]
  · norm_num [world12823, agent12823, scalar12823, tp12823, tm12823, ep12823, em12823, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12823, agent12823, tp12823, tm12823, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12823, agent12823, scalar12823, tp12823, tm12823, ep12823, em12823, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12823, agent12823, tp12823, tm12823, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12823, agent12823, scalar12823, tp12823, tm12823, ep12823, em12823, dsL]

theorem negative12823 :
    Eminus aL (agent12823.root+dsL) scalar12823.worldRadius world12823.frame
      agent12823.frame tm12823 ≤ -em12823 := by
  apply negative_check (lo := (3419911842473733709 / 5000000000000000000)) (hi := (68398236849474674181 / 100000000000000000000))
    (y := (-((14334152659723620231 / 20000000000000000000)))) (u := (488357464048481721 / 1000000000000000000))
  · norm_num [world12823, agent12823, scalar12823, tp12823, tm12823, ep12823, em12823, dsL]
  · norm_num [world12823, agent12823, scalar12823, tp12823, tm12823, ep12823, em12823, dsL]
  · norm_num [world12823, agent12823, scalar12823, tp12823, tm12823, ep12823, em12823, dsL]
  · norm_num [world12823, agent12823, scalar12823, tp12823, tm12823, ep12823, em12823, dsL]
  · norm_num [world12823, agent12823, scalar12823, tp12823, tm12823, ep12823, em12823, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12823, agent12823, tp12823, tm12823, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12823, agent12823, tp12823, tm12823, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12823, agent12823, scalar12823, tp12823, tm12823, ep12823, em12823, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12823, agent12823, tp12823, tm12823, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12823, agent12823, scalar12823, tp12823, tm12823, ep12823, em12823, dsL]

theorem tails12823 :
    exp (-((12823:ℝ)*ep12823)) ≤ scalar12823.upperTail ∧
    exp (-((12823:ℝ)*em12823)) ≤ scalar12823.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12823:ℝ)) (by norm_num [ep12823]) ?_)
      (show bp12823^8 ≤ scalar12823.upperTail by norm_num [bp12823, scalar12823])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12823, bp12823, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12823:ℝ)) (by norm_num [em12823]) ?_)
      (show bm12823^8 ≤ scalar12823.lowerTail by norm_num [bm12823, scalar12823])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12823, bm12823, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12823 :
    agent12823.root+dsL+scalar12823.worldRadius < √(1/100/aL) ∧
    2*(agent12823.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12823, agent12823, scalar12823, tp12823, tm12823, ep12823, em12823, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12823, agent12823, scalar12823, tp12823, tm12823, ep12823, em12823, dsL]

noncomputable def master12823 : MasterCertificate 12823 world12823 agent12823 :=
  master scalar12823 dsL tp12823 tm12823 ep12823 em12823
    (by norm_num [dsL]) (by norm_num [tp12823]) (by norm_num [tm12823])
    (by norm_num [ep12823]) (by norm_num [em12823])
    positive12823 negative12823 tails12823.1 tails12823.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12823.1 tailGuards12823.2

theorem preserves12823 : master12823.toScalarCertificate = scalar12823 := rfl

noncomputable def tp12824 : ℝ := (290961023 / 1250000000)
noncomputable def tm12824 : ℝ := (-((1217532301 / 2000000000)))
noncomputable def ep12824 : ℝ := (51757549568305463 / 100000000000000000000)
noncomputable def em12824 : ℝ := (50398641485433909 / 100000000000000000000)
noncomputable def bp12824 : ℝ := (8723833422347229101 / 20000000000000000000)
noncomputable def bm12824 : ℝ := (22289880414891242687 / 50000000000000000000)

theorem positive12824 :
    Eplus aL (agent12824.root+dsL) scalar12824.worldRadius world12824.frame
      agent12824.frame tp12824 ≤ -ep12824 := by
  apply positive_check (eT := (115630636819343027301 / 100000000000000000000)) (y := (18974153386565941237 / 50000000000000000000)) (u := (146152888268538111047 / 100000000000000000000))
  · norm_num [world12824, agent12824, scalar12824, tp12824, tm12824, ep12824, em12824, dsL]
  · norm_num [world12824, agent12824, scalar12824, tp12824, tm12824, ep12824, em12824, dsL]
  · norm_num [world12824, agent12824, scalar12824, tp12824, tm12824, ep12824, em12824, dsL]
  · norm_num [world12824, agent12824, scalar12824, tp12824, tm12824, ep12824, em12824, dsL]
  · norm_num [world12824, agent12824, scalar12824, tp12824, tm12824, ep12824, em12824, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12824, agent12824, tp12824, tm12824, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12824, agent12824, scalar12824, tp12824, tm12824, ep12824, em12824, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12824, agent12824, tp12824, tm12824, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12824, agent12824, scalar12824, tp12824, tm12824, ep12824, em12824, dsL]

theorem negative12824 :
    Eminus aL (agent12824.root+dsL) scalar12824.worldRadius world12824.frame
      agent12824.frame tm12824 ≤ -em12824 := by
  apply negative_check (lo := (68398064302015601843 / 100000000000000000000)) (hi := (17099516075503900461 / 25000000000000000000))
    (y := (-((8958848503120126533 / 12500000000000000000)))) (u := (24417867164777772863 / 50000000000000000000))
  · norm_num [world12824, agent12824, scalar12824, tp12824, tm12824, ep12824, em12824, dsL]
  · norm_num [world12824, agent12824, scalar12824, tp12824, tm12824, ep12824, em12824, dsL]
  · norm_num [world12824, agent12824, scalar12824, tp12824, tm12824, ep12824, em12824, dsL]
  · norm_num [world12824, agent12824, scalar12824, tp12824, tm12824, ep12824, em12824, dsL]
  · norm_num [world12824, agent12824, scalar12824, tp12824, tm12824, ep12824, em12824, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12824, agent12824, tp12824, tm12824, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12824, agent12824, tp12824, tm12824, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12824, agent12824, scalar12824, tp12824, tm12824, ep12824, em12824, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12824, agent12824, tp12824, tm12824, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12824, agent12824, scalar12824, tp12824, tm12824, ep12824, em12824, dsL]

theorem tails12824 :
    exp (-((12824:ℝ)*ep12824)) ≤ scalar12824.upperTail ∧
    exp (-((12824:ℝ)*em12824)) ≤ scalar12824.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12824:ℝ)) (by norm_num [ep12824]) ?_)
      (show bp12824^8 ≤ scalar12824.upperTail by norm_num [bp12824, scalar12824])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12824, bp12824, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12824:ℝ)) (by norm_num [em12824]) ?_)
      (show bm12824^8 ≤ scalar12824.lowerTail by norm_num [bm12824, scalar12824])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12824, bm12824, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12824 :
    agent12824.root+dsL+scalar12824.worldRadius < √(1/100/aL) ∧
    2*(agent12824.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12824, agent12824, scalar12824, tp12824, tm12824, ep12824, em12824, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12824, agent12824, scalar12824, tp12824, tm12824, ep12824, em12824, dsL]

noncomputable def master12824 : MasterCertificate 12824 world12824 agent12824 :=
  master scalar12824 dsL tp12824 tm12824 ep12824 em12824
    (by norm_num [dsL]) (by norm_num [tp12824]) (by norm_num [tm12824])
    (by norm_num [ep12824]) (by norm_num [em12824])
    positive12824 negative12824 tails12824.1 tails12824.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12824.1 tailGuards12824.2

theorem preserves12824 : master12824.toScalarCertificate = scalar12824 := rfl

end BstLean.Part268
