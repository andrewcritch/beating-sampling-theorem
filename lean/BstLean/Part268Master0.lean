import BstLean.Part261Checker
import BstLean.Part268Scalar0
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12350 : ℝ := (456373047 / 2000000000)
noncomputable def tm12350 : ℝ := (-((2992934283 / 5000000000)))
noncomputable def ep12350 : ℝ := (50383569697944957 / 100000000000000000000)
noncomputable def em12350 : ℝ := (12300081214214623 / 25000000000000000000)
noncomputable def bp12350 : ℝ := (45941728824333268157 / 100000000000000000000)
noncomputable def bm12350 : ℝ := (2924289218028556447 / 6250000000000000000)

theorem positive12350 :
    Eplus aL (agent12350.root+dsL) scalar12350.worldRadius world12350.frame
      agent12350.frame tp12350 ≤ -ep12350 := by
  apply positive_check (eT := (57738268607057397861 / 50000000000000000000)) (y := (18793440789757406337 / 50000000000000000000)) (u := (18203201043045001729 / 12500000000000000000))
  · norm_num [world12350, agent12350, scalar12350, tp12350, tm12350, ep12350, em12350, dsL]
  · norm_num [world12350, agent12350, scalar12350, tp12350, tm12350, ep12350, em12350, dsL]
  · norm_num [world12350, agent12350, scalar12350, tp12350, tm12350, ep12350, em12350, dsL]
  · norm_num [world12350, agent12350, scalar12350, tp12350, tm12350, ep12350, em12350, dsL]
  · norm_num [world12350, agent12350, scalar12350, tp12350, tm12350, ep12350, em12350, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12350, agent12350, tp12350, tm12350, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12350, agent12350, scalar12350, tp12350, tm12350, ep12350, em12350, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12350, agent12350, tp12350, tm12350, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12350, agent12350, scalar12350, tp12350, tm12350, ep12350, em12350, dsL]

theorem negative12350 :
    Eminus aL (agent12350.root+dsL) scalar12350.worldRadius world12350.frame
      agent12350.frame tm12350 ≤ -em12350 := by
  apply negative_check (lo := (8569869721426327179 / 12500000000000000000)) (hi := (68558957771410617433 / 100000000000000000000))
    (y := (-((8963087984660513833 / 12500000000000000000)))) (u := (24409587041226325291 / 50000000000000000000))
  · norm_num [world12350, agent12350, scalar12350, tp12350, tm12350, ep12350, em12350, dsL]
  · norm_num [world12350, agent12350, scalar12350, tp12350, tm12350, ep12350, em12350, dsL]
  · norm_num [world12350, agent12350, scalar12350, tp12350, tm12350, ep12350, em12350, dsL]
  · norm_num [world12350, agent12350, scalar12350, tp12350, tm12350, ep12350, em12350, dsL]
  · norm_num [world12350, agent12350, scalar12350, tp12350, tm12350, ep12350, em12350, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12350, agent12350, tp12350, tm12350, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12350, agent12350, tp12350, tm12350, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12350, agent12350, scalar12350, tp12350, tm12350, ep12350, em12350, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12350, agent12350, tp12350, tm12350, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12350, agent12350, scalar12350, tp12350, tm12350, ep12350, em12350, dsL]

theorem tails12350 :
    exp (-((12350:ℝ)*ep12350)) ≤ scalar12350.upperTail ∧
    exp (-((12350:ℝ)*em12350)) ≤ scalar12350.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12350:ℝ)) (by norm_num [ep12350]) ?_)
      (show bp12350^8 ≤ scalar12350.upperTail by norm_num [bp12350, scalar12350])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12350, bp12350, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12350:ℝ)) (by norm_num [em12350]) ?_)
      (show bm12350^8 ≤ scalar12350.lowerTail by norm_num [bm12350, scalar12350])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12350, bm12350, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12350 :
    agent12350.root+dsL+scalar12350.worldRadius < √(1/100/aL) ∧
    2*(agent12350.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12350, agent12350, scalar12350, tp12350, tm12350, ep12350, em12350, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12350, agent12350, scalar12350, tp12350, tm12350, ep12350, em12350, dsL]

noncomputable def master12350 : MasterCertificate 12350 world12350 agent12350 :=
  master scalar12350 dsL tp12350 tm12350 ep12350 em12350
    (by norm_num [dsL]) (by norm_num [tp12350]) (by norm_num [tm12350])
    (by norm_num [ep12350]) (by norm_num [em12350])
    positive12350 negative12350 tails12350.1 tails12350.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12350.1 tailGuards12350.2

theorem preserves12350 : master12350.toScalarCertificate = scalar12350 := rfl

noncomputable def tp12351 : ℝ := (228196319 / 1000000000)
noncomputable def tm12351 : ℝ := (-((2993040711 / 5000000000)))
noncomputable def ep12351 : ℝ := (2519331260158137 / 5000000000000000000)
noncomputable def em12351 : ℝ := (24601486117104941 / 50000000000000000000)
noncomputable def bp12351 : ℝ := (22968334250087246967 / 50000000000000000000)
noncomputable def bm12351 : ℝ := (46783837860030415543 / 100000000000000000000)

theorem positive12351 :
    Eplus aL (agent12351.root+dsL) scalar12351.worldRadius world12351.frame
      agent12351.frame tp12351 ≤ -ep12351 := by
  apply positive_check (eT := (57738432166094866877 / 50000000000000000000)) (y := (37587807076559859849 / 100000000000000000000)) (u := (9101684756956177177 / 6250000000000000000))
  · norm_num [world12351, agent12351, scalar12351, tp12351, tm12351, ep12351, em12351, dsL]
  · norm_num [world12351, agent12351, scalar12351, tp12351, tm12351, ep12351, em12351, dsL]
  · norm_num [world12351, agent12351, scalar12351, tp12351, tm12351, ep12351, em12351, dsL]
  · norm_num [world12351, agent12351, scalar12351, tp12351, tm12351, ep12351, em12351, dsL]
  · norm_num [world12351, agent12351, scalar12351, tp12351, tm12351, ep12351, em12351, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12351, agent12351, tp12351, tm12351, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12351, agent12351, scalar12351, tp12351, tm12351, ep12351, em12351, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12351, agent12351, tp12351, tm12351, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12351, agent12351, scalar12351, tp12351, tm12351, ep12351, em12351, dsL]

theorem negative12351 :
    Eminus aL (agent12351.root+dsL) scalar12351.worldRadius world12351.frame
      agent12351.frame tm12351 ≤ -em12351 := by
  apply negative_check (lo := (17139659745319061893 / 25000000000000000000)) (hi := (68558638981276247573 / 100000000000000000000))
    (y := (-((71704923670649911861 / 100000000000000000000)))) (u := (48819066781264698903 / 100000000000000000000))
  · norm_num [world12351, agent12351, scalar12351, tp12351, tm12351, ep12351, em12351, dsL]
  · norm_num [world12351, agent12351, scalar12351, tp12351, tm12351, ep12351, em12351, dsL]
  · norm_num [world12351, agent12351, scalar12351, tp12351, tm12351, ep12351, em12351, dsL]
  · norm_num [world12351, agent12351, scalar12351, tp12351, tm12351, ep12351, em12351, dsL]
  · norm_num [world12351, agent12351, scalar12351, tp12351, tm12351, ep12351, em12351, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12351, agent12351, tp12351, tm12351, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12351, agent12351, tp12351, tm12351, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12351, agent12351, scalar12351, tp12351, tm12351, ep12351, em12351, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12351, agent12351, tp12351, tm12351, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12351, agent12351, scalar12351, tp12351, tm12351, ep12351, em12351, dsL]

theorem tails12351 :
    exp (-((12351:ℝ)*ep12351)) ≤ scalar12351.upperTail ∧
    exp (-((12351:ℝ)*em12351)) ≤ scalar12351.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12351:ℝ)) (by norm_num [ep12351]) ?_)
      (show bp12351^8 ≤ scalar12351.upperTail by norm_num [bp12351, scalar12351])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12351, bp12351, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12351:ℝ)) (by norm_num [em12351]) ?_)
      (show bm12351^8 ≤ scalar12351.lowerTail by norm_num [bm12351, scalar12351])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12351, bm12351, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12351 :
    agent12351.root+dsL+scalar12351.worldRadius < √(1/100/aL) ∧
    2*(agent12351.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12351, agent12351, scalar12351, tp12351, tm12351, ep12351, em12351, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12351, agent12351, scalar12351, tp12351, tm12351, ep12351, em12351, dsL]

noncomputable def master12351 : MasterCertificate 12351 world12351 agent12351 :=
  master scalar12351 dsL tp12351 tm12351 ep12351 em12351
    (by norm_num [dsL]) (by norm_num [tp12351]) (by norm_num [tm12351])
    (by norm_num [ep12351]) (by norm_num [em12351])
    positive12351 negative12351 tails12351.1 tails12351.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12351.1 tailGuards12351.2

theorem preserves12351 : master12351.toScalarCertificate = scalar12351 := rfl

noncomputable def tp12352 : ℝ := (1141030557 / 5000000000)
noncomputable def tm12352 : ℝ := (-((187071687 / 312500000)))
noncomputable def ep12352 : ℝ := (10077935822133763 / 20000000000000000000)
noncomputable def em12352 : ℝ := (49205618126324999 / 100000000000000000000)
noncomputable def bp12352 : ℝ := (9186321903120815239 / 20000000000000000000)
noncomputable def bm12352 : ℝ := (23389524742520237583 / 50000000000000000000)

theorem positive12352 :
    Eplus aL (agent12352.root+dsL) scalar12352.worldRadius world12352.frame
      agent12352.frame tp12352 ≤ -ep12352 := by
  apply positive_check (eT := (2886929781410390389 / 2500000000000000000)) (y := (37588732674262654053 / 100000000000000000000)) (u := (72814152018648713277 / 50000000000000000000))
  · norm_num [world12352, agent12352, scalar12352, tp12352, tm12352, ep12352, em12352, dsL]
  · norm_num [world12352, agent12352, scalar12352, tp12352, tm12352, ep12352, em12352, dsL]
  · norm_num [world12352, agent12352, scalar12352, tp12352, tm12352, ep12352, em12352, dsL]
  · norm_num [world12352, agent12352, scalar12352, tp12352, tm12352, ep12352, em12352, dsL]
  · norm_num [world12352, agent12352, scalar12352, tp12352, tm12352, ep12352, em12352, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12352, agent12352, tp12352, tm12352, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12352, agent12352, scalar12352, tp12352, tm12352, ep12352, em12352, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12352, agent12352, tp12352, tm12352, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12352, agent12352, scalar12352, tp12352, tm12352, ep12352, em12352, dsL]

theorem negative12352 :
    Eminus aL (agent12352.root+dsL) scalar12352.worldRadius world12352.frame
      agent12352.frame tm12352 ≤ -em12352 := by
  apply negative_check (lo := (68558321406557830351 / 100000000000000000000)) (hi := (4284895087909864397 / 6250000000000000000))
    (y := (-((14341028396367203879 / 20000000000000000000)))) (u := (9763792040779459459 / 20000000000000000000))
  · norm_num [world12352, agent12352, scalar12352, tp12352, tm12352, ep12352, em12352, dsL]
  · norm_num [world12352, agent12352, scalar12352, tp12352, tm12352, ep12352, em12352, dsL]
  · norm_num [world12352, agent12352, scalar12352, tp12352, tm12352, ep12352, em12352, dsL]
  · norm_num [world12352, agent12352, scalar12352, tp12352, tm12352, ep12352, em12352, dsL]
  · norm_num [world12352, agent12352, scalar12352, tp12352, tm12352, ep12352, em12352, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12352, agent12352, tp12352, tm12352, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12352, agent12352, tp12352, tm12352, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12352, agent12352, scalar12352, tp12352, tm12352, ep12352, em12352, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12352, agent12352, tp12352, tm12352, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12352, agent12352, scalar12352, tp12352, tm12352, ep12352, em12352, dsL]

theorem tails12352 :
    exp (-((12352:ℝ)*ep12352)) ≤ scalar12352.upperTail ∧
    exp (-((12352:ℝ)*em12352)) ≤ scalar12352.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12352:ℝ)) (by norm_num [ep12352]) ?_)
      (show bp12352^8 ≤ scalar12352.upperTail by norm_num [bp12352, scalar12352])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12352, bp12352, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12352:ℝ)) (by norm_num [em12352]) ?_)
      (show bm12352^8 ≤ scalar12352.lowerTail by norm_num [bm12352, scalar12352])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12352, bm12352, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12352 :
    agent12352.root+dsL+scalar12352.worldRadius < √(1/100/aL) ∧
    2*(agent12352.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12352, agent12352, scalar12352, tp12352, tm12352, ep12352, em12352, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12352, agent12352, scalar12352, tp12352, tm12352, ep12352, em12352, dsL]

noncomputable def master12352 : MasterCertificate 12352 world12352 agent12352 :=
  master scalar12352 dsL tp12352 tm12352 ep12352 em12352
    (by norm_num [dsL]) (by norm_num [tp12352]) (by norm_num [tm12352])
    (by norm_num [ep12352]) (by norm_num [em12352])
    positive12352 negative12352 tails12352.1 tails12352.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12352.1 tailGuards12352.2

theorem preserves12352 : master12352.toScalarCertificate = scalar12352 := rfl

noncomputable def tp12353 : ℝ := (456431793 / 2000000000)
noncomputable def tm12353 : ℝ := (-((1496626617 / 2500000000)))
noncomputable def ep12353 : ℝ := (50392730967654777 / 100000000000000000000)
noncomputable def em12353 : ℝ := (49208262102201389 / 100000000000000000000)
noncomputable def bp12353 : ℝ := (5740819023961561059 / 12500000000000000000)
noncomputable def bm12353 : ℝ := (46774262674755934143 / 100000000000000000000)

theorem positive12353 :
    Eplus aL (agent12353.root+dsL) scalar12353.worldRadius world12353.frame
      agent12353.frame tp12353 ≤ -ep12353 := by
  apply positive_check (eT := (14434689710116626271 / 12500000000000000000)) (y := (37589657474514410739 / 100000000000000000000)) (u := (14562965081444728211 / 10000000000000000000))
  · norm_num [world12353, agent12353, scalar12353, tp12353, tm12353, ep12353, em12353, dsL]
  · norm_num [world12353, agent12353, scalar12353, tp12353, tm12353, ep12353, em12353, dsL]
  · norm_num [world12353, agent12353, scalar12353, tp12353, tm12353, ep12353, em12353, dsL]
  · norm_num [world12353, agent12353, scalar12353, tp12353, tm12353, ep12353, em12353, dsL]
  · norm_num [world12353, agent12353, scalar12353, tp12353, tm12353, ep12353, em12353, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12353, agent12353, tp12353, tm12353, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12353, agent12353, scalar12353, tp12353, tm12353, ep12353, em12353, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12353, agent12353, tp12353, tm12353, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12353, agent12353, scalar12353, tp12353, tm12353, ep12353, em12353, dsL]

theorem negative12353 :
    Eminus aL (agent12353.root+dsL) scalar12353.worldRadius world12353.frame
      agent12353.frame tm12353 ≤ -em12353 := by
  apply negative_check (lo := (68558004113442676063 / 100000000000000000000)) (hi := (2142437628545083627 / 3125000000000000000))
    (y := (-((14341071996806288973 / 20000000000000000000)))) (u := (48818853777608274777 / 100000000000000000000))
  · norm_num [world12353, agent12353, scalar12353, tp12353, tm12353, ep12353, em12353, dsL]
  · norm_num [world12353, agent12353, scalar12353, tp12353, tm12353, ep12353, em12353, dsL]
  · norm_num [world12353, agent12353, scalar12353, tp12353, tm12353, ep12353, em12353, dsL]
  · norm_num [world12353, agent12353, scalar12353, tp12353, tm12353, ep12353, em12353, dsL]
  · norm_num [world12353, agent12353, scalar12353, tp12353, tm12353, ep12353, em12353, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12353, agent12353, tp12353, tm12353, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12353, agent12353, tp12353, tm12353, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12353, agent12353, scalar12353, tp12353, tm12353, ep12353, em12353, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12353, agent12353, tp12353, tm12353, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12353, agent12353, scalar12353, tp12353, tm12353, ep12353, em12353, dsL]

theorem tails12353 :
    exp (-((12353:ℝ)*ep12353)) ≤ scalar12353.upperTail ∧
    exp (-((12353:ℝ)*em12353)) ≤ scalar12353.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12353:ℝ)) (by norm_num [ep12353]) ?_)
      (show bp12353^8 ≤ scalar12353.upperTail by norm_num [bp12353, scalar12353])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12353, bp12353, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12353:ℝ)) (by norm_num [em12353]) ?_)
      (show bm12353^8 ≤ scalar12353.lowerTail by norm_num [bm12353, scalar12353])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12353, bm12353, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12353 :
    agent12353.root+dsL+scalar12353.worldRadius < √(1/100/aL) ∧
    2*(agent12353.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12353, agent12353, scalar12353, tp12353, tm12353, ep12353, em12353, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12353, agent12353, scalar12353, tp12353, tm12353, ep12353, em12353, dsL]

noncomputable def master12353 : MasterCertificate 12353 world12353 agent12353 :=
  master scalar12353 dsL tp12353 tm12353 ep12353 em12353
    (by norm_num [dsL]) (by norm_num [tp12353]) (by norm_num [tm12353])
    (by norm_num [ep12353]) (by norm_num [em12353])
    positive12353 negative12353 tails12353.1 tails12353.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12353.1 tailGuards12353.2

theorem preserves12353 : master12353.toScalarCertificate = scalar12353 := rfl

noncomputable def tp12354 : ℝ := (1141128429 / 5000000000)
noncomputable def tm12354 : ℝ := (-((7663 / 12800)))
noncomputable def ep12354 : ℝ := (50395781372725069 / 100000000000000000000)
noncomputable def em12354 : ℝ := (4921090473855941 / 10000000000000000000)
noncomputable def bp12354 : ℝ := (45921496103870999469 / 100000000000000000000)
noncomputable def bm12354 : ℝ := (11692369253150916419 / 25000000000000000000)

theorem positive12354 :
    Eplus aL (agent12354.root+dsL) scalar12354.worldRadius world12354.frame
      agent12354.frame tp12354 ≤ -ep12354 := by
  apply positive_check (eT := (5773892222157748927 / 5000000000000000000)) (y := (9397645853178029019 / 25000000000000000000)) (u := (1165047994090033923 / 800000000000000000))
  · norm_num [world12354, agent12354, scalar12354, tp12354, tm12354, ep12354, em12354, dsL]
  · norm_num [world12354, agent12354, scalar12354, tp12354, tm12354, ep12354, em12354, dsL]
  · norm_num [world12354, agent12354, scalar12354, tp12354, tm12354, ep12354, em12354, dsL]
  · norm_num [world12354, agent12354, scalar12354, tp12354, tm12354, ep12354, em12354, dsL]
  · norm_num [world12354, agent12354, scalar12354, tp12354, tm12354, ep12354, em12354, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12354, agent12354, tp12354, tm12354, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12354, agent12354, scalar12354, tp12354, tm12354, ep12354, em12354, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12354, agent12354, tp12354, tm12354, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12354, agent12354, scalar12354, tp12354, tm12354, ep12354, em12354, dsL]

theorem negative12354 :
    Eminus aL (agent12354.root+dsL) scalar12354.worldRadius world12354.frame
      agent12354.frame tm12354 ≤ -em12354 := by
  apply negative_check (lo := (6855768763793594433 / 10000000000000000000)) (hi := (68557687637935944331 / 100000000000000000000))
    (y := (-((71705576707760065467 / 100000000000000000000)))) (u := (24409373987841373543 / 50000000000000000000))
  · norm_num [world12354, agent12354, scalar12354, tp12354, tm12354, ep12354, em12354, dsL]
  · norm_num [world12354, agent12354, scalar12354, tp12354, tm12354, ep12354, em12354, dsL]
  · norm_num [world12354, agent12354, scalar12354, tp12354, tm12354, ep12354, em12354, dsL]
  · norm_num [world12354, agent12354, scalar12354, tp12354, tm12354, ep12354, em12354, dsL]
  · norm_num [world12354, agent12354, scalar12354, tp12354, tm12354, ep12354, em12354, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12354, agent12354, tp12354, tm12354, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12354, agent12354, tp12354, tm12354, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12354, agent12354, scalar12354, tp12354, tm12354, ep12354, em12354, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12354, agent12354, tp12354, tm12354, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12354, agent12354, scalar12354, tp12354, tm12354, ep12354, em12354, dsL]

theorem tails12354 :
    exp (-((12354:ℝ)*ep12354)) ≤ scalar12354.upperTail ∧
    exp (-((12354:ℝ)*em12354)) ≤ scalar12354.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12354:ℝ)) (by norm_num [ep12354]) ?_)
      (show bp12354^8 ≤ scalar12354.upperTail by norm_num [bp12354, scalar12354])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12354, bp12354, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12354:ℝ)) (by norm_num [em12354]) ?_)
      (show bm12354^8 ≤ scalar12354.lowerTail by norm_num [bm12354, scalar12354])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12354, bm12354, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12354 :
    agent12354.root+dsL+scalar12354.worldRadius < √(1/100/aL) ∧
    2*(agent12354.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12354, agent12354, scalar12354, tp12354, tm12354, ep12354, em12354, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12354, agent12354, scalar12354, tp12354, tm12354, ep12354, em12354, dsL]

noncomputable def master12354 : MasterCertificate 12354 world12354 agent12354 :=
  master scalar12354 dsL tp12354 tm12354 ep12354 em12354
    (by norm_num [dsL]) (by norm_num [tp12354]) (by norm_num [tm12354])
    (by norm_num [ep12354]) (by norm_num [em12354])
    positive12354 negative12354 tails12354.1 tails12354.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12354.1 tailGuards12354.2

theorem preserves12354 : master12354.toScalarCertificate = scalar12354 := rfl

noncomputable def tp12355 : ℝ := (1141177319 / 5000000000)
noncomputable def tm12355 : ℝ := (-((37418319 / 62500000)))
noncomputable def ep12355 : ℝ := (2015953212986397 / 4000000000000000000)
noncomputable def em12355 : ℝ := (24606773020120209 / 50000000000000000000)
noncomputable def bp12355 : ℝ := (45916441252968923901 / 100000000000000000000)
noncomputable def bm12355 : ℝ := (1461396640470933063 / 3125000000000000000)

theorem positive12355 :
    Eplus aL (agent12355.root+dsL) scalar12355.worldRadius world12355.frame
      agent12355.frame tp12355 ≤ -ep12355 := by
  apply positive_check (eT := (57739085207231245477 / 50000000000000000000)) (y := (37591507849387416407 / 100000000000000000000)) (u := (36408086383461181741 / 25000000000000000000))
  · norm_num [world12355, agent12355, scalar12355, tp12355, tm12355, ep12355, em12355, dsL]
  · norm_num [world12355, agent12355, scalar12355, tp12355, tm12355, ep12355, em12355, dsL]
  · norm_num [world12355, agent12355, scalar12355, tp12355, tm12355, ep12355, em12355, dsL]
  · norm_num [world12355, agent12355, scalar12355, tp12355, tm12355, ep12355, em12355, dsL]
  · norm_num [world12355, agent12355, scalar12355, tp12355, tm12355, ep12355, em12355, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12355, agent12355, tp12355, tm12355, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12355, agent12355, scalar12355, tp12355, tm12355, ep12355, em12355, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12355, agent12355, tp12355, tm12355, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12355, agent12355, scalar12355, tp12355, tm12355, ep12355, em12355, dsL]

theorem negative12355 :
    Eminus aL (agent12355.root+dsL) scalar12355.worldRadius world12355.frame
      agent12355.frame tm12355 ≤ -em12355 := by
  apply negative_check (lo := (34278685536082526557 / 50000000000000000000)) (hi := (13711474214433010623 / 20000000000000000000))
    (y := (-((71705794636810687243 / 100000000000000000000)))) (u := (12204660396391171443 / 25000000000000000000))
  · norm_num [world12355, agent12355, scalar12355, tp12355, tm12355, ep12355, em12355, dsL]
  · norm_num [world12355, agent12355, scalar12355, tp12355, tm12355, ep12355, em12355, dsL]
  · norm_num [world12355, agent12355, scalar12355, tp12355, tm12355, ep12355, em12355, dsL]
  · norm_num [world12355, agent12355, scalar12355, tp12355, tm12355, ep12355, em12355, dsL]
  · norm_num [world12355, agent12355, scalar12355, tp12355, tm12355, ep12355, em12355, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12355, agent12355, tp12355, tm12355, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12355, agent12355, tp12355, tm12355, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12355, agent12355, scalar12355, tp12355, tm12355, ep12355, em12355, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12355, agent12355, tp12355, tm12355, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12355, agent12355, scalar12355, tp12355, tm12355, ep12355, em12355, dsL]

theorem tails12355 :
    exp (-((12355:ℝ)*ep12355)) ≤ scalar12355.upperTail ∧
    exp (-((12355:ℝ)*em12355)) ≤ scalar12355.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12355:ℝ)) (by norm_num [ep12355]) ?_)
      (show bp12355^8 ≤ scalar12355.upperTail by norm_num [bp12355, scalar12355])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12355, bp12355, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12355:ℝ)) (by norm_num [em12355]) ?_)
      (show bm12355^8 ≤ scalar12355.lowerTail by norm_num [bm12355, scalar12355])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12355, bm12355, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12355 :
    agent12355.root+dsL+scalar12355.worldRadius < √(1/100/aL) ∧
    2*(agent12355.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12355, agent12355, scalar12355, tp12355, tm12355, ep12355, em12355, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12355, agent12355, scalar12355, tp12355, tm12355, ep12355, em12355, dsL]

noncomputable def master12355 : MasterCertificate 12355 world12355 agent12355 :=
  master scalar12355 dsL tp12355 tm12355 ep12355 em12355
    (by norm_num [dsL]) (by norm_num [tp12355]) (by norm_num [tm12355])
    (by norm_num [ep12355]) (by norm_num [em12355])
    positive12355 negative12355 tails12355.1 tails12355.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12355.1 tailGuards12355.2

theorem preserves12355 : master12355.toScalarCertificate = scalar12355 := rfl

noncomputable def tp12356 : ℝ := (570613083 / 2500000000)
noncomputable def tm12356 : ℝ := (-((5987143231 / 10000000000)))
noncomputable def ep12356 : ℝ := (10080375603132631 / 20000000000000000000)
noncomputable def em12356 : ℝ := (24608093069384113 / 50000000000000000000)
noncomputable def bp12356 : ℝ := (45911387502658527047 / 100000000000000000000)
noncomputable def bm12356 : ℝ := (23379954513575022457 / 50000000000000000000)

theorem positive12356 :
    Eplus aL (agent12356.root+dsL) scalar12356.worldRadius world12356.frame
      agent12356.frame tp12356 ≤ -ep12356 := by
  apply positive_check (eT := (5773924789574020979 / 5000000000000000000)) (y := (37592431312165808081 / 100000000000000000000)) (u := (72816845200279346487 / 50000000000000000000))
  · norm_num [world12356, agent12356, scalar12356, tp12356, tm12356, ep12356, em12356, dsL]
  · norm_num [world12356, agent12356, scalar12356, tp12356, tm12356, ep12356, em12356, dsL]
  · norm_num [world12356, agent12356, scalar12356, tp12356, tm12356, ep12356, em12356, dsL]
  · norm_num [world12356, agent12356, scalar12356, tp12356, tm12356, ep12356, em12356, dsL]
  · norm_num [world12356, agent12356, scalar12356, tp12356, tm12356, ep12356, em12356, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12356, agent12356, tp12356, tm12356, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12356, agent12356, scalar12356, tp12356, tm12356, ep12356, em12356, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12356, agent12356, tp12356, tm12356, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12356, agent12356, scalar12356, tp12356, tm12356, ep12356, em12356, dsL]

theorem negative12356 :
    Eminus aL (agent12356.root+dsL) scalar12356.worldRadius world12356.frame
      agent12356.frame tm12356 ≤ -em12356 := by
  apply negative_check (lo := (8569631859836468201 / 12500000000000000000)) (hi := (68557054878691745609 / 100000000000000000000))
    (y := (-((17926503148420503773 / 25000000000000000000)))) (u := (12204633795524204499 / 25000000000000000000))
  · norm_num [world12356, agent12356, scalar12356, tp12356, tm12356, ep12356, em12356, dsL]
  · norm_num [world12356, agent12356, scalar12356, tp12356, tm12356, ep12356, em12356, dsL]
  · norm_num [world12356, agent12356, scalar12356, tp12356, tm12356, ep12356, em12356, dsL]
  · norm_num [world12356, agent12356, scalar12356, tp12356, tm12356, ep12356, em12356, dsL]
  · norm_num [world12356, agent12356, scalar12356, tp12356, tm12356, ep12356, em12356, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12356, agent12356, tp12356, tm12356, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12356, agent12356, tp12356, tm12356, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12356, agent12356, scalar12356, tp12356, tm12356, ep12356, em12356, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12356, agent12356, tp12356, tm12356, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12356, agent12356, scalar12356, tp12356, tm12356, ep12356, em12356, dsL]

theorem tails12356 :
    exp (-((12356:ℝ)*ep12356)) ≤ scalar12356.upperTail ∧
    exp (-((12356:ℝ)*em12356)) ≤ scalar12356.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12356:ℝ)) (by norm_num [ep12356]) ?_)
      (show bp12356^8 ≤ scalar12356.upperTail by norm_num [bp12356, scalar12356])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12356, bp12356, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12356:ℝ)) (by norm_num [em12356]) ?_)
      (show bm12356^8 ≤ scalar12356.lowerTail by norm_num [bm12356, scalar12356])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12356, bm12356, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12356 :
    agent12356.root+dsL+scalar12356.worldRadius < √(1/100/aL) ∧
    2*(agent12356.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12356, agent12356, scalar12356, tp12356, tm12356, ep12356, em12356, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12356, agent12356, scalar12356, tp12356, tm12356, ep12356, em12356, dsL]

noncomputable def master12356 : MasterCertificate 12356 world12356 agent12356 :=
  master scalar12356 dsL tp12356 tm12356 ep12356 em12356
    (by norm_num [dsL]) (by norm_num [tp12356]) (by norm_num [tm12356])
    (by norm_num [ep12356]) (by norm_num [em12356])
    positive12356 negative12356 tails12356.1 tails12356.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12356.1 tailGuards12356.2

theorem preserves12356 : master12356.toScalarCertificate = scalar12356 := rfl

noncomputable def tp12357 : ℝ := (228255003 / 1000000000)
noncomputable def tm12357 : ℝ := (-((5987355177 / 10000000000)))
noncomputable def ep12357 : ℝ := (50404923655122107 / 100000000000000000000)
noncomputable def em12357 : ℝ := (24609412163124543 / 50000000000000000000)
noncomputable def bp12357 : ℝ := (22953167706762071063 / 50000000000000000000)
noncomputable def bm12357 : ℝ := (9351025424013595039 / 20000000000000000000)

theorem positive12357 :
    Eplus aL (agent12357.root+dsL) scalar12357.worldRadius world12357.frame
      agent12357.frame tp12357 ≤ -ep12357 := by
  apply positive_check (eT := (7217426326845233343 / 6250000000000000000)) (y := (37593355440003217207 / 100000000000000000000)) (u := (145635036248250997767 / 100000000000000000000))
  · norm_num [world12357, agent12357, scalar12357, tp12357, tm12357, ep12357, em12357, dsL]
  · norm_num [world12357, agent12357, scalar12357, tp12357, tm12357, ep12357, em12357, dsL]
  · norm_num [world12357, agent12357, scalar12357, tp12357, tm12357, ep12357, em12357, dsL]
  · norm_num [world12357, agent12357, scalar12357, tp12357, tm12357, ep12357, em12357, dsL]
  · norm_num [world12357, agent12357, scalar12357, tp12357, tm12357, ep12357, em12357, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12357, agent12357, tp12357, tm12357, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12357, agent12357, scalar12357, tp12357, tm12357, ep12357, em12357, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12357, agent12357, tp12357, tm12357, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12357, agent12357, scalar12357, tp12357, tm12357, ep12357, em12357, dsL]

theorem negative12357 :
    Eminus aL (agent12357.root+dsL) scalar12357.worldRadius world12357.frame
      agent12357.frame tm12357 ≤ -em12357 := by
  apply negative_check (lo := (13711347937721286107 / 20000000000000000000)) (hi := (8569592461075803817 / 12500000000000000000))
    (y := (-((286824916028295419 / 400000000000000000)))) (u := (4881842953236330411 / 10000000000000000000))
  · norm_num [world12357, agent12357, scalar12357, tp12357, tm12357, ep12357, em12357, dsL]
  · norm_num [world12357, agent12357, scalar12357, tp12357, tm12357, ep12357, em12357, dsL]
  · norm_num [world12357, agent12357, scalar12357, tp12357, tm12357, ep12357, em12357, dsL]
  · norm_num [world12357, agent12357, scalar12357, tp12357, tm12357, ep12357, em12357, dsL]
  · norm_num [world12357, agent12357, scalar12357, tp12357, tm12357, ep12357, em12357, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12357, agent12357, tp12357, tm12357, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12357, agent12357, tp12357, tm12357, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12357, agent12357, scalar12357, tp12357, tm12357, ep12357, em12357, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12357, agent12357, tp12357, tm12357, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12357, agent12357, scalar12357, tp12357, tm12357, ep12357, em12357, dsL]

theorem tails12357 :
    exp (-((12357:ℝ)*ep12357)) ≤ scalar12357.upperTail ∧
    exp (-((12357:ℝ)*em12357)) ≤ scalar12357.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12357:ℝ)) (by norm_num [ep12357]) ?_)
      (show bp12357^8 ≤ scalar12357.upperTail by norm_num [bp12357, scalar12357])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12357, bp12357, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12357:ℝ)) (by norm_num [em12357]) ?_)
      (show bm12357^8 ≤ scalar12357.lowerTail by norm_num [bm12357, scalar12357])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12357, bm12357, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12357 :
    agent12357.root+dsL+scalar12357.worldRadius < √(1/100/aL) ∧
    2*(agent12357.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12357, agent12357, scalar12357, tp12357, tm12357, ep12357, em12357, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12357, agent12357, scalar12357, tp12357, tm12357, ep12357, em12357, dsL]

noncomputable def master12357 : MasterCertificate 12357 world12357 agent12357 :=
  master scalar12357 dsL tp12357 tm12357 ep12357 em12357
    (by norm_num [dsL]) (by norm_num [tp12357]) (by norm_num [tm12357])
    (by norm_num [ep12357]) (by norm_num [em12357])
    positive12357 negative12357 tails12357.1 tails12357.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12357.1 tailGuards12357.2

theorem preserves12357 : master12357.toScalarCertificate = scalar12357 := rfl

noncomputable def tp12358 : ℝ := (142665481 / 625000000)
noncomputable def tm12358 : ℝ := (-((5987567207 / 10000000000)))
noncomputable def ep12358 : ℝ := (25203984153815101 / 50000000000000000000)
noncomputable def em12358 : ℝ := (12305365401073597 / 25000000000000000000)
noncomputable def bp12358 : ℝ := (22950642115316102803 / 50000000000000000000)
noncomputable def bm12358 : ℝ := (46750346050440204379 / 100000000000000000000)

theorem positive12358 :
    Eplus aL (agent12358.root+dsL) scalar12358.worldRadius world12358.frame
      agent12358.frame tp12358 ≤ -ep12358 := by
  apply positive_check (eT := (115479146466460321003 / 100000000000000000000)) (y := (37594279347581386897 / 100000000000000000000)) (u := (145636381787603125983 / 100000000000000000000))
  · norm_num [world12358, agent12358, scalar12358, tp12358, tm12358, ep12358, em12358, dsL]
  · norm_num [world12358, agent12358, scalar12358, tp12358, tm12358, ep12358, em12358, dsL]
  · norm_num [world12358, agent12358, scalar12358, tp12358, tm12358, ep12358, em12358, dsL]
  · norm_num [world12358, agent12358, scalar12358, tp12358, tm12358, ep12358, em12358, dsL]
  · norm_num [world12358, agent12358, scalar12358, tp12358, tm12358, ep12358, em12358, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12358, agent12358, tp12358, tm12358, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12358, agent12358, scalar12358, tp12358, tm12358, ep12358, em12358, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12358, agent12358, tp12358, tm12358, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12358, agent12358, scalar12358, tp12358, tm12358, ep12358, em12358, dsL]

theorem negative12358 :
    Eminus aL (agent12358.root+dsL) scalar12358.worldRadius world12358.frame
      agent12358.frame tm12358 ≤ -em12358 := by
  apply negative_check (lo := (68556424079766655597 / 100000000000000000000)) (hi := (34278212039883327799 / 50000000000000000000))
    (y := (-((35853223543944492899 / 50000000000000000000)))) (u := (48818323068850334047 / 100000000000000000000))
  · norm_num [world12358, agent12358, scalar12358, tp12358, tm12358, ep12358, em12358, dsL]
  · norm_num [world12358, agent12358, scalar12358, tp12358, tm12358, ep12358, em12358, dsL]
  · norm_num [world12358, agent12358, scalar12358, tp12358, tm12358, ep12358, em12358, dsL]
  · norm_num [world12358, agent12358, scalar12358, tp12358, tm12358, ep12358, em12358, dsL]
  · norm_num [world12358, agent12358, scalar12358, tp12358, tm12358, ep12358, em12358, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12358, agent12358, tp12358, tm12358, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12358, agent12358, tp12358, tm12358, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12358, agent12358, scalar12358, tp12358, tm12358, ep12358, em12358, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12358, agent12358, tp12358, tm12358, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12358, agent12358, scalar12358, tp12358, tm12358, ep12358, em12358, dsL]

theorem tails12358 :
    exp (-((12358:ℝ)*ep12358)) ≤ scalar12358.upperTail ∧
    exp (-((12358:ℝ)*em12358)) ≤ scalar12358.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12358:ℝ)) (by norm_num [ep12358]) ?_)
      (show bp12358^8 ≤ scalar12358.upperTail by norm_num [bp12358, scalar12358])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12358, bp12358, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12358:ℝ)) (by norm_num [em12358]) ?_)
      (show bm12358^8 ≤ scalar12358.lowerTail by norm_num [bm12358, scalar12358])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12358, bm12358, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12358 :
    agent12358.root+dsL+scalar12358.worldRadius < √(1/100/aL) ∧
    2*(agent12358.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12358, agent12358, scalar12358, tp12358, tm12358, ep12358, em12358, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12358, agent12358, scalar12358, tp12358, tm12358, ep12358, em12358, dsL]

noncomputable def master12358 : MasterCertificate 12358 world12358 agent12358 :=
  master scalar12358 dsL tp12358 tm12358 ep12358 em12358
    (by norm_num [dsL]) (by norm_num [tp12358]) (by norm_num [tm12358])
    (by norm_num [ep12358]) (by norm_num [em12358])
    positive12358 negative12358 tails12358.1 tails12358.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12358.1 tailGuards12358.2

theorem preserves12358 : master12358.toScalarCertificate = scalar12358 := rfl

noncomputable def tp12359 : ℝ := (2282745293 / 10000000000)
noncomputable def tm12359 : ℝ := (-((5987778877 / 10000000000)))
noncomputable def ep12359 : ℝ := (157534409522887 / 312500000000000000)
noncomputable def em12359 : ℝ := (24612048561319541 / 50000000000000000000)
noncomputable def bp12359 : ℝ := (45896234610449588351 / 100000000000000000000)
noncomputable def bm12359 : ℝ := (46745566432297141951 / 100000000000000000000)

theorem positive12359 :
    Eplus aL (agent12359.root+dsL) scalar12359.worldRadius world12359.frame
      agent12359.frame tp12359 ≤ -ep12359 := by
  apply positive_check (eT := (11547947123295142217 / 10000000000000000000)) (y := (18797601289637650117 / 50000000000000000000)) (u := (145637726355044384597 / 100000000000000000000))
  · norm_num [world12359, agent12359, scalar12359, tp12359, tm12359, ep12359, em12359, dsL]
  · norm_num [world12359, agent12359, scalar12359, tp12359, tm12359, ep12359, em12359, dsL]
  · norm_num [world12359, agent12359, scalar12359, tp12359, tm12359, ep12359, em12359, dsL]
  · norm_num [world12359, agent12359, scalar12359, tp12359, tm12359, ep12359, em12359, dsL]
  · norm_num [world12359, agent12359, scalar12359, tp12359, tm12359, ep12359, em12359, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12359, agent12359, tp12359, tm12359, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12359, agent12359, scalar12359, tp12359, tm12359, ep12359, em12359, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12359, agent12359, tp12359, tm12359, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12359, agent12359, scalar12359, tp12359, tm12359, ep12359, em12359, dsL]

theorem negative12359 :
    Eminus aL (agent12359.root+dsL) scalar12359.worldRadius world12359.frame
      agent12359.frame tm12359 ≤ -em12359 := by
  apply negative_check (lo := (17139027492816320399 / 25000000000000000000)) (hi := (68556109971265281597 / 100000000000000000000))
    (y := (-((14341332523167381559 / 20000000000000000000)))) (u := (24409108925916899951 / 50000000000000000000))
  · norm_num [world12359, agent12359, scalar12359, tp12359, tm12359, ep12359, em12359, dsL]
  · norm_num [world12359, agent12359, scalar12359, tp12359, tm12359, ep12359, em12359, dsL]
  · norm_num [world12359, agent12359, scalar12359, tp12359, tm12359, ep12359, em12359, dsL]
  · norm_num [world12359, agent12359, scalar12359, tp12359, tm12359, ep12359, em12359, dsL]
  · norm_num [world12359, agent12359, scalar12359, tp12359, tm12359, ep12359, em12359, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12359, agent12359, tp12359, tm12359, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12359, agent12359, tp12359, tm12359, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12359, agent12359, scalar12359, tp12359, tm12359, ep12359, em12359, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12359, agent12359, tp12359, tm12359, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12359, agent12359, scalar12359, tp12359, tm12359, ep12359, em12359, dsL]

theorem tails12359 :
    exp (-((12359:ℝ)*ep12359)) ≤ scalar12359.upperTail ∧
    exp (-((12359:ℝ)*em12359)) ≤ scalar12359.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12359:ℝ)) (by norm_num [ep12359]) ?_)
      (show bp12359^8 ≤ scalar12359.upperTail by norm_num [bp12359, scalar12359])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12359, bp12359, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12359:ℝ)) (by norm_num [em12359]) ?_)
      (show bm12359^8 ≤ scalar12359.lowerTail by norm_num [bm12359, scalar12359])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12359, bm12359, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12359 :
    agent12359.root+dsL+scalar12359.worldRadius < √(1/100/aL) ∧
    2*(agent12359.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12359, agent12359, scalar12359, tp12359, tm12359, ep12359, em12359, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12359, agent12359, scalar12359, tp12359, tm12359, ep12359, em12359, dsL]

noncomputable def master12359 : MasterCertificate 12359 world12359 agent12359 :=
  master scalar12359 dsL tp12359 tm12359 ep12359 em12359
    (by norm_num [dsL]) (by norm_num [tp12359]) (by norm_num [tm12359])
    (by norm_num [ep12359]) (by norm_num [em12359])
    positive12359 negative12359 tails12359.1 tails12359.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12359.1 tailGuards12359.2

theorem preserves12359 : master12359.toScalarCertificate = scalar12359 := rfl

noncomputable def tp12360 : ℝ := (2282920193 / 10000000000)
noncomputable def tm12360 : ℝ := (-((5988224241 / 10000000000)))
noncomputable def ep12360 : ℝ := (12603886420404863 / 25000000000000000000)
noncomputable def em12360 : ℝ := (3076772168094737 / 6250000000000000000)
noncomputable def bp12360 : ℝ := (45890127427544004349 / 100000000000000000000)
noncomputable def bm12360 : ℝ := (5842451956878107517 / 12500000000000000000)

theorem positive12360 :
    Eplus aL (agent12360.root+dsL) scalar12360.worldRadius world12360.frame
      agent12360.frame tp12360 ≤ -ep12360 := by
  apply positive_check (eT := (115480358845283382107 / 100000000000000000000)) (y := (37595388881925119139 / 100000000000000000000)) (u := (2912759953644809297 / 2000000000000000000))
  · norm_num [world12360, agent12360, scalar12360, tp12360, tm12360, ep12360, em12360, dsL]
  · norm_num [world12360, agent12360, scalar12360, tp12360, tm12360, ep12360, em12360, dsL]
  · norm_num [world12360, agent12360, scalar12360, tp12360, tm12360, ep12360, em12360, dsL]
  · norm_num [world12360, agent12360, scalar12360, tp12360, tm12360, ep12360, em12360, dsL]
  · norm_num [world12360, agent12360, scalar12360, tp12360, tm12360, ep12360, em12360, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12360, agent12360, tp12360, tm12360, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12360, agent12360, scalar12360, tp12360, tm12360, ep12360, em12360, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12360, agent12360, tp12360, tm12360, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12360, agent12360, scalar12360, tp12360, tm12360, ep12360, em12360, dsL]

theorem negative12360 :
    Eminus aL (agent12360.root+dsL) scalar12360.worldRadius world12360.frame
      agent12360.frame tm12360 ≤ -em12360 := by
  apply negative_check (lo := (17138696435136818091 / 25000000000000000000)) (hi := (13710957148109454473 / 20000000000000000000))
    (y := (-((14340986205284589629 / 20000000000000000000)))) (u := (9763812638049016023 / 20000000000000000000))
  · norm_num [world12360, agent12360, scalar12360, tp12360, tm12360, ep12360, em12360, dsL]
  · norm_num [world12360, agent12360, scalar12360, tp12360, tm12360, ep12360, em12360, dsL]
  · norm_num [world12360, agent12360, scalar12360, tp12360, tm12360, ep12360, em12360, dsL]
  · norm_num [world12360, agent12360, scalar12360, tp12360, tm12360, ep12360, em12360, dsL]
  · norm_num [world12360, agent12360, scalar12360, tp12360, tm12360, ep12360, em12360, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12360, agent12360, tp12360, tm12360, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12360, agent12360, tp12360, tm12360, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12360, agent12360, scalar12360, tp12360, tm12360, ep12360, em12360, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12360, agent12360, tp12360, tm12360, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12360, agent12360, scalar12360, tp12360, tm12360, ep12360, em12360, dsL]

theorem tails12360 :
    exp (-((12360:ℝ)*ep12360)) ≤ scalar12360.upperTail ∧
    exp (-((12360:ℝ)*em12360)) ≤ scalar12360.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12360:ℝ)) (by norm_num [ep12360]) ?_)
      (show bp12360^8 ≤ scalar12360.upperTail by norm_num [bp12360, scalar12360])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12360, bp12360, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12360:ℝ)) (by norm_num [em12360]) ?_)
      (show bm12360^8 ≤ scalar12360.lowerTail by norm_num [bm12360, scalar12360])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12360, bm12360, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12360 :
    agent12360.root+dsL+scalar12360.worldRadius < √(1/100/aL) ∧
    2*(agent12360.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12360, agent12360, scalar12360, tp12360, tm12360, ep12360, em12360, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12360, agent12360, scalar12360, tp12360, tm12360, ep12360, em12360, dsL]

noncomputable def master12360 : MasterCertificate 12360 world12360 agent12360 :=
  master scalar12360 dsL tp12360 tm12360 ep12360 em12360
    (by norm_num [dsL]) (by norm_num [tp12360]) (by norm_num [tm12360])
    (by norm_num [ep12360]) (by norm_num [em12360])
    positive12360 negative12360 tails12360.1 tails12360.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12360.1 tailGuards12360.2

theorem preserves12360 : master12360.toScalarCertificate = scalar12360 := rfl

noncomputable def tp12361 : ℝ := (1141508837 / 5000000000)
noncomputable def tm12361 : ℝ := (-((748554457 / 1250000000)))
noncomputable def ep12361 : ℝ := (12604646460046097 / 25000000000000000000)
noncomputable def em12361 : ℝ := (49230987793455009 / 100000000000000000000)
noncomputable def bp12361 : ℝ := (917701601620962099 / 2000000000000000000)
noncomputable def bm12361 : ℝ := (4673483816678594473 / 10000000000000000000)

theorem positive12361 :
    Eplus aL (agent12361.root+dsL) scalar12361.worldRadius world12361.frame
      agent12361.frame tp12361 ≤ -ep12361 := by
  apply positive_check (eT := (57740341409773304361 / 50000000000000000000)) (y := (37596310901400422403 / 100000000000000000000)) (u := (18204917562391630493 / 12500000000000000000))
  · norm_num [world12361, agent12361, scalar12361, tp12361, tm12361, ep12361, em12361, dsL]
  · norm_num [world12361, agent12361, scalar12361, tp12361, tm12361, ep12361, em12361, dsL]
  · norm_num [world12361, agent12361, scalar12361, tp12361, tm12361, ep12361, em12361, dsL]
  · norm_num [world12361, agent12361, scalar12361, tp12361, tm12361, ep12361, em12361, dsL]
  · norm_num [world12361, agent12361, scalar12361, tp12361, tm12361, ep12361, em12361, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12361, agent12361, tp12361, tm12361, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12361, agent12361, scalar12361, tp12361, tm12361, ep12361, em12361, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12361, agent12361, tp12361, tm12361, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12361, agent12361, scalar12361, tp12361, tm12361, ep12361, em12361, dsL]

theorem negative12361 :
    Eminus aL (agent12361.root+dsL) scalar12361.worldRadius world12361.frame
      agent12361.frame tm12361 ≤ -em12361 := by
  apply negative_check (lo := (34277236325418030309 / 50000000000000000000)) (hi := (68554472650836060619 / 100000000000000000000))
    (y := (-((71705145610911723249 / 100000000000000000000)))) (u := (48818958432220305809 / 100000000000000000000))
  · norm_num [world12361, agent12361, scalar12361, tp12361, tm12361, ep12361, em12361, dsL]
  · norm_num [world12361, agent12361, scalar12361, tp12361, tm12361, ep12361, em12361, dsL]
  · norm_num [world12361, agent12361, scalar12361, tp12361, tm12361, ep12361, em12361, dsL]
  · norm_num [world12361, agent12361, scalar12361, tp12361, tm12361, ep12361, em12361, dsL]
  · norm_num [world12361, agent12361, scalar12361, tp12361, tm12361, ep12361, em12361, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12361, agent12361, tp12361, tm12361, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12361, agent12361, tp12361, tm12361, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12361, agent12361, scalar12361, tp12361, tm12361, ep12361, em12361, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12361, agent12361, tp12361, tm12361, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12361, agent12361, scalar12361, tp12361, tm12361, ep12361, em12361, dsL]

theorem tails12361 :
    exp (-((12361:ℝ)*ep12361)) ≤ scalar12361.upperTail ∧
    exp (-((12361:ℝ)*em12361)) ≤ scalar12361.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12361:ℝ)) (by norm_num [ep12361]) ?_)
      (show bp12361^8 ≤ scalar12361.upperTail by norm_num [bp12361, scalar12361])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12361, bp12361, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12361:ℝ)) (by norm_num [em12361]) ?_)
      (show bm12361^8 ≤ scalar12361.lowerTail by norm_num [bm12361, scalar12361])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12361, bm12361, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12361 :
    agent12361.root+dsL+scalar12361.worldRadius < √(1/100/aL) ∧
    2*(agent12361.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12361, agent12361, scalar12361, tp12361, tm12361, ep12361, em12361, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12361, agent12361, scalar12361, tp12361, tm12361, ep12361, em12361, dsL]

noncomputable def master12361 : MasterCertificate 12361 world12361 agent12361 :=
  master scalar12361 dsL tp12361 tm12361 ep12361 em12361
    (by norm_num [dsL]) (by norm_num [tp12361]) (by norm_num [tm12361])
    (by norm_num [ep12361]) (by norm_num [em12361])
    positive12361 negative12361 tails12361.1 tails12361.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12361.1 tailGuards12361.2

theorem preserves12361 : master12361.toScalarCertificate = scalar12361 := rfl

noncomputable def tp12362 : ℝ := (285389391 / 1250000000)
noncomputable def tm12362 : ℝ := (-((5988647151 / 10000000000)))
noncomputable def ep12362 : ℝ := (25210811973724993 / 50000000000000000000)
noncomputable def em12362 : ℝ := (24616809493431707 / 50000000000000000000)
noncomputable def bp12362 : ℝ := (45880034395283142487 / 100000000000000000000)
noncomputable def bm12362 : ℝ := (4673006223885224401 / 10000000000000000000)

theorem positive12362 :
    Eplus aL (agent12362.root+dsL) scalar12362.worldRadius world12362.frame
      agent12362.frame tp12362 ≤ -ep12362 := by
  apply positive_check (eT := (14435125828646321043 / 12500000000000000000)) (y := (9399308259112340683 / 25000000000000000000)) (u := (145640683496728948249 / 100000000000000000000))
  · norm_num [world12362, agent12362, scalar12362, tp12362, tm12362, ep12362, em12362, dsL]
  · norm_num [world12362, agent12362, scalar12362, tp12362, tm12362, ep12362, em12362, dsL]
  · norm_num [world12362, agent12362, scalar12362, tp12362, tm12362, ep12362, em12362, dsL]
  · norm_num [world12362, agent12362, scalar12362, tp12362, tm12362, ep12362, em12362, dsL]
  · norm_num [world12362, agent12362, scalar12362, tp12362, tm12362, ep12362, em12362, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12362, agent12362, tp12362, tm12362, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12362, agent12362, scalar12362, tp12362, tm12362, ep12362, em12362, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12362, agent12362, tp12362, tm12362, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12362, agent12362, scalar12362, tp12362, tm12362, ep12362, em12362, dsL]

theorem negative12362 :
    Eminus aL (agent12362.root+dsL) scalar12362.worldRadius world12362.frame
      agent12362.frame tm12362 ≤ -em12362 := by
  apply negative_check (lo := (34277079579807891549 / 50000000000000000000)) (hi := (68554159159615783099 / 100000000000000000000))
    (y := (-((35852680926418171397 / 50000000000000000000)))) (u := (48818852865279152793 / 100000000000000000000))
  · norm_num [world12362, agent12362, scalar12362, tp12362, tm12362, ep12362, em12362, dsL]
  · norm_num [world12362, agent12362, scalar12362, tp12362, tm12362, ep12362, em12362, dsL]
  · norm_num [world12362, agent12362, scalar12362, tp12362, tm12362, ep12362, em12362, dsL]
  · norm_num [world12362, agent12362, scalar12362, tp12362, tm12362, ep12362, em12362, dsL]
  · norm_num [world12362, agent12362, scalar12362, tp12362, tm12362, ep12362, em12362, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12362, agent12362, tp12362, tm12362, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12362, agent12362, tp12362, tm12362, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12362, agent12362, scalar12362, tp12362, tm12362, ep12362, em12362, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12362, agent12362, tp12362, tm12362, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12362, agent12362, scalar12362, tp12362, tm12362, ep12362, em12362, dsL]

theorem tails12362 :
    exp (-((12362:ℝ)*ep12362)) ≤ scalar12362.upperTail ∧
    exp (-((12362:ℝ)*em12362)) ≤ scalar12362.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12362:ℝ)) (by norm_num [ep12362]) ?_)
      (show bp12362^8 ≤ scalar12362.upperTail by norm_num [bp12362, scalar12362])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12362, bp12362, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12362:ℝ)) (by norm_num [em12362]) ?_)
      (show bm12362^8 ≤ scalar12362.lowerTail by norm_num [bm12362, scalar12362])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12362, bm12362, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12362 :
    agent12362.root+dsL+scalar12362.worldRadius < √(1/100/aL) ∧
    2*(agent12362.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12362, agent12362, scalar12362, tp12362, tm12362, ep12362, em12362, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12362, agent12362, scalar12362, tp12362, tm12362, ep12362, em12362, dsL]

noncomputable def master12362 : MasterCertificate 12362 world12362 agent12362 :=
  master scalar12362 dsL tp12362 tm12362 ep12362 em12362
    (by norm_num [dsL]) (by norm_num [tp12362]) (by norm_num [tm12362])
    (by norm_num [ep12362]) (by norm_num [em12362])
    positive12362 negative12362 tails12362.1 tails12362.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12362.1 tailGuards12362.2

theorem preserves12362 : master12362.toScalarCertificate = scalar12362 := rfl

noncomputable def tp12363 : ℝ := (1141606263 / 5000000000)
noncomputable def tm12363 : ℝ := (-((1497214623 / 2500000000)))
noncomputable def ep12363 : ℝ := (25212330143229547 / 50000000000000000000)
noncomputable def em12363 : ℝ := (49236248571160687 / 100000000000000000000)
noncomputable def bp12363 : ℝ := (45874990169515647891 / 100000000000000000000)
noncomputable def bm12363 : ℝ := (46725287653530565861 / 100000000000000000000)

theorem positive12363 :
    Eplus aL (agent12363.root+dsL) scalar12363.worldRadius world12363.frame
      agent12363.frame tp12363 ≤ -ep12363 := by
  apply positive_check (eT := (115481330063050109027 / 100000000000000000000)) (y := (7519630914665236921 / 20000000000000000000)) (u := (145642025635519168481 / 100000000000000000000))
  · norm_num [world12363, agent12363, scalar12363, tp12363, tm12363, ep12363, em12363, dsL]
  · norm_num [world12363, agent12363, scalar12363, tp12363, tm12363, ep12363, em12363, dsL]
  · norm_num [world12363, agent12363, scalar12363, tp12363, tm12363, ep12363, em12363, dsL]
  · norm_num [world12363, agent12363, scalar12363, tp12363, tm12363, ep12363, em12363, dsL]
  · norm_num [world12363, agent12363, scalar12363, tp12363, tm12363, ep12363, em12363, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12363, agent12363, tp12363, tm12363, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12363, agent12363, scalar12363, tp12363, tm12363, ep12363, em12363, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12363, agent12363, tp12363, tm12363, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12363, agent12363, scalar12363, tp12363, tm12363, ep12363, em12363, dsL]

theorem negative12363 :
    Eminus aL (agent12363.root+dsL) scalar12363.worldRadius world12363.frame
      agent12363.frame tm12363 ≤ -em12363 := by
  apply negative_check (lo := (17138461569550711623 / 25000000000000000000)) (hi := (68553846278202846493 / 100000000000000000000))
    (y := (-((71705577282230210977 / 100000000000000000000)))) (u := (48818747695233615359 / 100000000000000000000))
  · norm_num [world12363, agent12363, scalar12363, tp12363, tm12363, ep12363, em12363, dsL]
  · norm_num [world12363, agent12363, scalar12363, tp12363, tm12363, ep12363, em12363, dsL]
  · norm_num [world12363, agent12363, scalar12363, tp12363, tm12363, ep12363, em12363, dsL]
  · norm_num [world12363, agent12363, scalar12363, tp12363, tm12363, ep12363, em12363, dsL]
  · norm_num [world12363, agent12363, scalar12363, tp12363, tm12363, ep12363, em12363, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12363, agent12363, tp12363, tm12363, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12363, agent12363, tp12363, tm12363, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12363, agent12363, scalar12363, tp12363, tm12363, ep12363, em12363, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12363, agent12363, tp12363, tm12363, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12363, agent12363, scalar12363, tp12363, tm12363, ep12363, em12363, dsL]

theorem tails12363 :
    exp (-((12363:ℝ)*ep12363)) ≤ scalar12363.upperTail ∧
    exp (-((12363:ℝ)*em12363)) ≤ scalar12363.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12363:ℝ)) (by norm_num [ep12363]) ?_)
      (show bp12363^8 ≤ scalar12363.upperTail by norm_num [bp12363, scalar12363])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12363, bp12363, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12363:ℝ)) (by norm_num [em12363]) ?_)
      (show bm12363^8 ≤ scalar12363.lowerTail by norm_num [bm12363, scalar12363])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12363, bm12363, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12363 :
    agent12363.root+dsL+scalar12363.worldRadius < √(1/100/aL) ∧
    2*(agent12363.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12363, agent12363, scalar12363, tp12363, tm12363, ep12363, em12363, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12363, agent12363, scalar12363, tp12363, tm12363, ep12363, em12363, dsL]

noncomputable def master12363 : MasterCertificate 12363 world12363 agent12363 :=
  master scalar12363 dsL tp12363 tm12363 ep12363 em12363
    (by norm_num [dsL]) (by norm_num [tp12363]) (by norm_num [tm12363])
    (by norm_num [ep12363]) (by norm_num [em12363])
    positive12363 negative12363 tails12363.1 tails12363.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12363.1 tailGuards12363.2

theorem preserves12363 : master12363.toScalarCertificate = scalar12363 := rfl

noncomputable def tp12364 : ℝ := (1141655089 / 5000000000)
noncomputable def tm12364 : ℝ := (-((74863383 / 125000000)))
noncomputable def ep12364 : ℝ := (5042770138879469 / 10000000000000000000)
noncomputable def em12364 : ℝ := (24619441712433227 / 50000000000000000000)
noncomputable def bp12364 : ℝ := (45869942773320408267 / 100000000000000000000)
noncomputable def bm12364 : ℝ := (11680127361012305351 / 25000000000000000000)

theorem positive12364 :
    Eplus aL (agent12364.root+dsL) scalar12364.worldRadius world12364.frame
      agent12364.frame tp12364 ≤ -ep12364 := by
  apply positive_check (eT := (57740827688990064699 / 50000000000000000000)) (y := (939976831789486113 / 2500000000000000000)) (u := (145643363652410853849 / 100000000000000000000))
  · norm_num [world12364, agent12364, scalar12364, tp12364, tm12364, ep12364, em12364, dsL]
  · norm_num [world12364, agent12364, scalar12364, tp12364, tm12364, ep12364, em12364, dsL]
  · norm_num [world12364, agent12364, scalar12364, tp12364, tm12364, ep12364, em12364, dsL]
  · norm_num [world12364, agent12364, scalar12364, tp12364, tm12364, ep12364, em12364, dsL]
  · norm_num [world12364, agent12364, scalar12364, tp12364, tm12364, ep12364, em12364, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12364, agent12364, tp12364, tm12364, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12364, agent12364, scalar12364, tp12364, tm12364, ep12364, em12364, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12364, agent12364, tp12364, tm12364, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12364, agent12364, scalar12364, tp12364, tm12364, ep12364, em12364, dsL]

theorem negative12364 :
    Eminus aL (agent12364.root+dsL) scalar12364.worldRadius world12364.frame
      agent12364.frame tm12364 ≤ -em12364 := by
  apply negative_check (lo := (68553529853495452197 / 100000000000000000000)) (hi := (34276764926747726099 / 50000000000000000000))
    (y := (-((35852892991727832287 / 50000000000000000000)))) (u := (48818645810015242193 / 100000000000000000000))
  · norm_num [world12364, agent12364, scalar12364, tp12364, tm12364, ep12364, em12364, dsL]
  · norm_num [world12364, agent12364, scalar12364, tp12364, tm12364, ep12364, em12364, dsL]
  · norm_num [world12364, agent12364, scalar12364, tp12364, tm12364, ep12364, em12364, dsL]
  · norm_num [world12364, agent12364, scalar12364, tp12364, tm12364, ep12364, em12364, dsL]
  · norm_num [world12364, agent12364, scalar12364, tp12364, tm12364, ep12364, em12364, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12364, agent12364, tp12364, tm12364, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12364, agent12364, tp12364, tm12364, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12364, agent12364, scalar12364, tp12364, tm12364, ep12364, em12364, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12364, agent12364, tp12364, tm12364, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12364, agent12364, scalar12364, tp12364, tm12364, ep12364, em12364, dsL]

theorem tails12364 :
    exp (-((12364:ℝ)*ep12364)) ≤ scalar12364.upperTail ∧
    exp (-((12364:ℝ)*em12364)) ≤ scalar12364.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12364:ℝ)) (by norm_num [ep12364]) ?_)
      (show bp12364^8 ≤ scalar12364.upperTail by norm_num [bp12364, scalar12364])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12364, bp12364, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12364:ℝ)) (by norm_num [em12364]) ?_)
      (show bm12364^8 ≤ scalar12364.lowerTail by norm_num [bm12364, scalar12364])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12364, bm12364, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12364 :
    agent12364.root+dsL+scalar12364.worldRadius < √(1/100/aL) ∧
    2*(agent12364.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12364, agent12364, scalar12364, tp12364, tm12364, ep12364, em12364, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12364, agent12364, scalar12364, tp12364, tm12364, ep12364, em12364, dsL]

noncomputable def master12364 : MasterCertificate 12364 world12364 agent12364 :=
  master scalar12364 dsL tp12364 tm12364 ep12364 em12364
    (by norm_num [dsL]) (by norm_num [tp12364]) (by norm_num [tm12364])
    (by norm_num [ep12364]) (by norm_num [em12364])
    positive12364 negative12364 tails12364.1 tails12364.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12364.1 tailGuards12364.2

theorem preserves12364 : master12364.toScalarCertificate = scalar12364 := rfl

noncomputable def tp12365 : ℝ := (71356493 / 312500000)
noncomputable def tm12365 : ℝ := (-((239571301 / 400000000)))
noncomputable def ep12365 : ℝ := (2521537027218837 / 5000000000000000000)
noncomputable def em12365 : ℝ := (4924151653237809 / 10000000000000000000)
noncomputable def bp12365 : ℝ := (45864896963817607141 / 100000000000000000000)
noncomputable def bm12365 : ℝ := (729933323067385221 / 1562500000000000000)

theorem positive12365 :
    Eplus aL (agent12365.root+dsL) scalar12365.worldRadius world12365.frame
      agent12365.frame tp12365 ≤ -ep12365 := by
  apply positive_check (eT := (57740990165836957197 / 50000000000000000000)) (y := (37599991050254366627 / 100000000000000000000)) (u := (72822350171138906411 / 50000000000000000000))
  · norm_num [world12365, agent12365, scalar12365, tp12365, tm12365, ep12365, em12365, dsL]
  · norm_num [world12365, agent12365, scalar12365, tp12365, tm12365, ep12365, em12365, dsL]
  · norm_num [world12365, agent12365, scalar12365, tp12365, tm12365, ep12365, em12365, dsL]
  · norm_num [world12365, agent12365, scalar12365, tp12365, tm12365, ep12365, em12365, dsL]
  · norm_num [world12365, agent12365, scalar12365, tp12365, tm12365, ep12365, em12365, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12365, agent12365, tp12365, tm12365, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12365, agent12365, scalar12365, tp12365, tm12365, ep12365, em12365, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12365, agent12365, tp12365, tm12365, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12365, agent12365, scalar12365, tp12365, tm12365, ep12365, em12365, dsL]

theorem negative12365 :
    Eminus aL (agent12365.root+dsL) scalar12365.worldRadius world12365.frame
      agent12365.frame tm12365 ≤ -em12365 := by
  apply negative_check (lo := (34276607254892487457 / 50000000000000000000)) (hi := (13710642901956994983 / 20000000000000000000))
    (y := (-((71705991677405237547 / 100000000000000000000)))) (u := (48818545393117823309 / 100000000000000000000))
  · norm_num [world12365, agent12365, scalar12365, tp12365, tm12365, ep12365, em12365, dsL]
  · norm_num [world12365, agent12365, scalar12365, tp12365, tm12365, ep12365, em12365, dsL]
  · norm_num [world12365, agent12365, scalar12365, tp12365, tm12365, ep12365, em12365, dsL]
  · norm_num [world12365, agent12365, scalar12365, tp12365, tm12365, ep12365, em12365, dsL]
  · norm_num [world12365, agent12365, scalar12365, tp12365, tm12365, ep12365, em12365, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12365, agent12365, tp12365, tm12365, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12365, agent12365, tp12365, tm12365, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12365, agent12365, scalar12365, tp12365, tm12365, ep12365, em12365, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12365, agent12365, tp12365, tm12365, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12365, agent12365, scalar12365, tp12365, tm12365, ep12365, em12365, dsL]

theorem tails12365 :
    exp (-((12365:ℝ)*ep12365)) ≤ scalar12365.upperTail ∧
    exp (-((12365:ℝ)*em12365)) ≤ scalar12365.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12365:ℝ)) (by norm_num [ep12365]) ?_)
      (show bp12365^8 ≤ scalar12365.upperTail by norm_num [bp12365, scalar12365])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12365, bp12365, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12365:ℝ)) (by norm_num [em12365]) ?_)
      (show bm12365^8 ≤ scalar12365.lowerTail by norm_num [bm12365, scalar12365])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12365, bm12365, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12365 :
    agent12365.root+dsL+scalar12365.worldRadius < √(1/100/aL) ∧
    2*(agent12365.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12365, agent12365, scalar12365, tp12365, tm12365, ep12365, em12365, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12365, agent12365, scalar12365, tp12365, tm12365, ep12365, em12365, dsL]

noncomputable def master12365 : MasterCertificate 12365 world12365 agent12365 :=
  master scalar12365 dsL tp12365 tm12365 ep12365 em12365
    (by norm_num [dsL]) (by norm_num [tp12365]) (by norm_num [tm12365])
    (by norm_num [ep12365]) (by norm_num [em12365])
    positive12365 negative12365 tails12365.1 tails12365.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12365.1 tailGuards12365.2

theorem preserves12365 : master12365.toScalarCertificate = scalar12365 := rfl

noncomputable def tp12366 : ℝ := (2283505311 / 10000000000)
noncomputable def tm12366 : ℝ := (-((2994747151 / 5000000000)))
noncomputable def ep12366 : ℝ := (6304222322383051 / 12500000000000000000)
noncomputable def em12366 : ℝ := (49244148589746411 / 100000000000000000000)
noncomputable def bp12366 : ℝ := (9171970431101327159 / 20000000000000000000)
noncomputable def bm12366 : ℝ := (23355478423855820163 / 50000000000000000000)

theorem positive12366 :
    Eplus aL (agent12366.root+dsL) scalar12366.worldRadius world12366.frame
      agent12366.frame tp12366 ≤ -ep12366 := by
  apply positive_check (eT := (28870576214648369869 / 25000000000000000000)) (y := (37600908209536650091 / 100000000000000000000)) (u := (145646036142291853507 / 100000000000000000000))
  · norm_num [world12366, agent12366, scalar12366, tp12366, tm12366, ep12366, em12366, dsL]
  · norm_num [world12366, agent12366, scalar12366, tp12366, tm12366, ep12366, em12366, dsL]
  · norm_num [world12366, agent12366, scalar12366, tp12366, tm12366, ep12366, em12366, dsL]
  · norm_num [world12366, agent12366, scalar12366, tp12366, tm12366, ep12366, em12366, dsL]
  · norm_num [world12366, agent12366, scalar12366, tp12366, tm12366, ep12366, em12366, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12366, agent12366, tp12366, tm12366, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12366, agent12366, scalar12366, tp12366, tm12366, ep12366, em12366, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12366, agent12366, tp12366, tm12366, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12366, agent12366, scalar12366, tp12366, tm12366, ep12366, em12366, dsL]

theorem negative12366 :
    Eminus aL (agent12366.root+dsL) scalar12366.worldRadius world12366.frame
      agent12366.frame tm12366 ≤ -em12366 := by
  apply negative_check (lo := (8569112447153545803 / 12500000000000000000)) (hi := (2742115983089134657 / 4000000000000000000))
    (y := (-((35853098715316596789 / 50000000000000000000)))) (u := (48818444947488170887 / 100000000000000000000))
  · norm_num [world12366, agent12366, scalar12366, tp12366, tm12366, ep12366, em12366, dsL]
  · norm_num [world12366, agent12366, scalar12366, tp12366, tm12366, ep12366, em12366, dsL]
  · norm_num [world12366, agent12366, scalar12366, tp12366, tm12366, ep12366, em12366, dsL]
  · norm_num [world12366, agent12366, scalar12366, tp12366, tm12366, ep12366, em12366, dsL]
  · norm_num [world12366, agent12366, scalar12366, tp12366, tm12366, ep12366, em12366, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12366, agent12366, tp12366, tm12366, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12366, agent12366, tp12366, tm12366, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12366, agent12366, scalar12366, tp12366, tm12366, ep12366, em12366, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12366, agent12366, tp12366, tm12366, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12366, agent12366, scalar12366, tp12366, tm12366, ep12366, em12366, dsL]

theorem tails12366 :
    exp (-((12366:ℝ)*ep12366)) ≤ scalar12366.upperTail ∧
    exp (-((12366:ℝ)*em12366)) ≤ scalar12366.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12366:ℝ)) (by norm_num [ep12366]) ?_)
      (show bp12366^8 ≤ scalar12366.upperTail by norm_num [bp12366, scalar12366])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12366, bp12366, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12366:ℝ)) (by norm_num [em12366]) ?_)
      (show bm12366^8 ≤ scalar12366.lowerTail by norm_num [bm12366, scalar12366])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12366, bm12366, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12366 :
    agent12366.root+dsL+scalar12366.worldRadius < √(1/100/aL) ∧
    2*(agent12366.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12366, agent12366, scalar12366, tp12366, tm12366, ep12366, em12366, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12366, agent12366, scalar12366, tp12366, tm12366, ep12366, em12366, dsL]

noncomputable def master12366 : MasterCertificate 12366 world12366 agent12366 :=
  master scalar12366 dsL tp12366 tm12366 ep12366 em12366
    (by norm_num [dsL]) (by norm_num [tp12366]) (by norm_num [tm12366])
    (by norm_num [ep12366]) (by norm_num [em12366])
    positive12366 negative12366 tails12366.1 tails12366.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12366.1 tailGuards12366.2

theorem preserves12366 : master12366.toScalarCertificate = scalar12366 := rfl

noncomputable def tp12367 : ℝ := (570900713 / 2500000000)
noncomputable def tm12367 : ℝ := (-((5989706157 / 10000000000)))
noncomputable def ep12367 : ℝ := (12609203759320371 / 25000000000000000000)
noncomputable def em12367 : ℝ := (49246779175205449 / 100000000000000000000)
noncomputable def bp12367 : ℝ := (9170961734262163041 / 20000000000000000000)
noncomputable def bm12367 : ℝ := (2919136391422816117 / 6250000000000000000)

theorem positive12367 :
    Eplus aL (agent12367.root+dsL) scalar12367.worldRadius world12367.frame
      agent12367.frame tp12367 ≤ -ep12367 := by
  apply positive_check (eT := (115482629461067779209 / 100000000000000000000)) (y := (37601826017693012977 / 100000000000000000000)) (u := (145647372899625411233 / 100000000000000000000))
  · norm_num [world12367, agent12367, scalar12367, tp12367, tm12367, ep12367, em12367, dsL]
  · norm_num [world12367, agent12367, scalar12367, tp12367, tm12367, ep12367, em12367, dsL]
  · norm_num [world12367, agent12367, scalar12367, tp12367, tm12367, ep12367, em12367, dsL]
  · norm_num [world12367, agent12367, scalar12367, tp12367, tm12367, ep12367, em12367, dsL]
  · norm_num [world12367, agent12367, scalar12367, tp12367, tm12367, ep12367, em12367, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12367, agent12367, tp12367, tm12367, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12367, agent12367, scalar12367, tp12367, tm12367, ep12367, em12367, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12367, agent12367, tp12367, tm12367, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12367, agent12367, scalar12367, tp12367, tm12367, ep12367, em12367, dsL]

theorem negative12367 :
    Eminus aL (agent12367.root+dsL) scalar12367.worldRadius world12367.frame
      agent12367.frame tm12367 ≤ -em12367 := by
  apply negative_check (lo := (34276292126007276049 / 50000000000000000000)) (hi := (68552584252014552099 / 100000000000000000000))
    (y := (-((1434128098941172089 / 2000000000000000000)))) (u := (4881834364130138821 / 10000000000000000000))
  · norm_num [world12367, agent12367, scalar12367, tp12367, tm12367, ep12367, em12367, dsL]
  · norm_num [world12367, agent12367, scalar12367, tp12367, tm12367, ep12367, em12367, dsL]
  · norm_num [world12367, agent12367, scalar12367, tp12367, tm12367, ep12367, em12367, dsL]
  · norm_num [world12367, agent12367, scalar12367, tp12367, tm12367, ep12367, em12367, dsL]
  · norm_num [world12367, agent12367, scalar12367, tp12367, tm12367, ep12367, em12367, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12367, agent12367, tp12367, tm12367, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12367, agent12367, tp12367, tm12367, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12367, agent12367, scalar12367, tp12367, tm12367, ep12367, em12367, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12367, agent12367, tp12367, tm12367, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12367, agent12367, scalar12367, tp12367, tm12367, ep12367, em12367, dsL]

theorem tails12367 :
    exp (-((12367:ℝ)*ep12367)) ≤ scalar12367.upperTail ∧
    exp (-((12367:ℝ)*em12367)) ≤ scalar12367.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12367:ℝ)) (by norm_num [ep12367]) ?_)
      (show bp12367^8 ≤ scalar12367.upperTail by norm_num [bp12367, scalar12367])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12367, bp12367, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12367:ℝ)) (by norm_num [em12367]) ?_)
      (show bm12367^8 ≤ scalar12367.lowerTail by norm_num [bm12367, scalar12367])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12367, bm12367, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12367 :
    agent12367.root+dsL+scalar12367.worldRadius < √(1/100/aL) ∧
    2*(agent12367.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12367, agent12367, scalar12367, tp12367, tm12367, ep12367, em12367, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12367, agent12367, scalar12367, tp12367, tm12367, ep12367, em12367, dsL]

noncomputable def master12367 : MasterCertificate 12367 world12367 agent12367 :=
  master scalar12367 dsL tp12367 tm12367 ep12367 em12367
    (by norm_num [dsL]) (by norm_num [tp12367]) (by norm_num [tm12367])
    (by norm_num [ep12367]) (by norm_num [em12367])
    positive12367 negative12367 tails12367.1 tails12367.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12367.1 tailGuards12367.2

theorem preserves12367 : master12367.toScalarCertificate = scalar12367 := rfl

noncomputable def tp12368 : ℝ := (91348011 / 400000000)
noncomputable def tm12368 : ℝ := (-((299495887 / 500000000)))
noncomputable def ep12368 : ℝ := (25219924561724699 / 50000000000000000000)
noncomputable def em12368 : ℝ := (49249407576625791 / 100000000000000000000)
noncomputable def bp12368 : ℝ := (45849767075122216871 / 100000000000000000000)
noncomputable def bm12368 : ℝ := (23350704717804628137 / 50000000000000000000)

theorem positive12368 :
    Eplus aL (agent12368.root+dsL) scalar12368.worldRadius world12368.frame
      agent12368.frame tp12368 ≤ -ep12368 := by
  apply positive_check (eT := (23096590647284820649 / 20000000000000000000)) (y := (18801371164889000827 / 50000000000000000000)) (u := (29129741498043851427 / 20000000000000000000))
  · norm_num [world12368, agent12368, scalar12368, tp12368, tm12368, ep12368, em12368, dsL]
  · norm_num [world12368, agent12368, scalar12368, tp12368, tm12368, ep12368, em12368, dsL]
  · norm_num [world12368, agent12368, scalar12368, tp12368, tm12368, ep12368, em12368, dsL]
  · norm_num [world12368, agent12368, scalar12368, tp12368, tm12368, ep12368, em12368, dsL]
  · norm_num [world12368, agent12368, scalar12368, tp12368, tm12368, ep12368, em12368, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12368, agent12368, tp12368, tm12368, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12368, agent12368, scalar12368, tp12368, tm12368, ep12368, em12368, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12368, agent12368, tp12368, tm12368, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12368, agent12368, scalar12368, tp12368, tm12368, ep12368, em12368, dsL]

theorem negative12368 :
    Eminus aL (agent12368.root+dsL) scalar12368.worldRadius world12368.frame
      agent12368.frame tm12368 ≤ -em12368 := by
  apply negative_check (lo := (6855227004661701741 / 10000000000000000000)) (hi := (68552270046617017411 / 100000000000000000000))
    (y := (-((7170661064563705441 / 10000000000000000000)))) (u := (24409121611382887511 / 50000000000000000000))
  · norm_num [world12368, agent12368, scalar12368, tp12368, tm12368, ep12368, em12368, dsL]
  · norm_num [world12368, agent12368, scalar12368, tp12368, tm12368, ep12368, em12368, dsL]
  · norm_num [world12368, agent12368, scalar12368, tp12368, tm12368, ep12368, em12368, dsL]
  · norm_num [world12368, agent12368, scalar12368, tp12368, tm12368, ep12368, em12368, dsL]
  · norm_num [world12368, agent12368, scalar12368, tp12368, tm12368, ep12368, em12368, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12368, agent12368, tp12368, tm12368, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12368, agent12368, tp12368, tm12368, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12368, agent12368, scalar12368, tp12368, tm12368, ep12368, em12368, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12368, agent12368, tp12368, tm12368, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12368, agent12368, scalar12368, tp12368, tm12368, ep12368, em12368, dsL]

theorem tails12368 :
    exp (-((12368:ℝ)*ep12368)) ≤ scalar12368.upperTail ∧
    exp (-((12368:ℝ)*em12368)) ≤ scalar12368.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12368:ℝ)) (by norm_num [ep12368]) ?_)
      (show bp12368^8 ≤ scalar12368.upperTail by norm_num [bp12368, scalar12368])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12368, bp12368, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12368:ℝ)) (by norm_num [em12368]) ?_)
      (show bm12368^8 ≤ scalar12368.lowerTail by norm_num [bm12368, scalar12368])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12368, bm12368, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12368 :
    agent12368.root+dsL+scalar12368.worldRadius < √(1/100/aL) ∧
    2*(agent12368.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12368, agent12368, scalar12368, tp12368, tm12368, ep12368, em12368, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12368, agent12368, scalar12368, tp12368, tm12368, ep12368, em12368, dsL]

noncomputable def master12368 : MasterCertificate 12368 world12368 agent12368 :=
  master scalar12368 dsL tp12368 tm12368 ep12368 em12368
    (by norm_num [dsL]) (by norm_num [tp12368]) (by norm_num [tm12368])
    (by norm_num [ep12368]) (by norm_num [em12368])
    positive12368 negative12368 tails12368.1 tails12368.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12368.1 tailGuards12368.2

theorem preserves12368 : master12368.toScalarCertificate = scalar12368 := rfl

noncomputable def tp12369 : ℝ := (285474711 / 1250000000)
noncomputable def tm12369 : ℝ := (-((1497532309 / 2500000000)))
noncomputable def ep12369 : ℝ := (25221441282140607 / 50000000000000000000)
noncomputable def em12369 : ℝ := (24626017680564853 / 50000000000000000000)
noncomputable def bp12369 : ℝ := (45844726142924650277 / 100000000000000000000)
noncomputable def bm12369 : ℝ := (23348318617371727437 / 50000000000000000000)

theorem positive12369 :
    Eplus aL (agent12369.root+dsL) scalar12369.worldRadius world12369.frame
      agent12369.frame tp12369 ≤ -ep12369 := by
  apply positive_check (eT := (4619331078834475507 / 4000000000000000000)) (y := (4700457351049587769 / 12500000000000000000)) (u := (145650042335598595529 / 100000000000000000000))
  · norm_num [world12369, agent12369, scalar12369, tp12369, tm12369, ep12369, em12369, dsL]
  · norm_num [world12369, agent12369, scalar12369, tp12369, tm12369, ep12369, em12369, dsL]
  · norm_num [world12369, agent12369, scalar12369, tp12369, tm12369, ep12369, em12369, dsL]
  · norm_num [world12369, agent12369, scalar12369, tp12369, tm12369, ep12369, em12369, dsL]
  · norm_num [world12369, agent12369, scalar12369, tp12369, tm12369, ep12369, em12369, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12369, agent12369, tp12369, tm12369, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12369, agent12369, scalar12369, tp12369, tm12369, ep12369, em12369, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12369, agent12369, tp12369, tm12369, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12369, agent12369, scalar12369, tp12369, tm12369, ep12369, em12369, dsL]

theorem negative12369 :
    Eminus aL (agent12369.root+dsL) scalar12369.worldRadius world12369.frame
      agent12369.frame tm12369 ≤ -em12369 := by
  apply negative_check (lo := (8568994520196555907 / 12500000000000000000)) (hi := (68551956161572447257 / 100000000000000000000))
    (y := (-((71706816323667067481 / 100000000000000000000)))) (u := (12204535703617021597 / 25000000000000000000))
  · norm_num [world12369, agent12369, scalar12369, tp12369, tm12369, ep12369, em12369, dsL]
  · norm_num [world12369, agent12369, scalar12369, tp12369, tm12369, ep12369, em12369, dsL]
  · norm_num [world12369, agent12369, scalar12369, tp12369, tm12369, ep12369, em12369, dsL]
  · norm_num [world12369, agent12369, scalar12369, tp12369, tm12369, ep12369, em12369, dsL]
  · norm_num [world12369, agent12369, scalar12369, tp12369, tm12369, ep12369, em12369, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12369, agent12369, tp12369, tm12369, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12369, agent12369, tp12369, tm12369, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12369, agent12369, scalar12369, tp12369, tm12369, ep12369, em12369, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12369, agent12369, tp12369, tm12369, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12369, agent12369, scalar12369, tp12369, tm12369, ep12369, em12369, dsL]

theorem tails12369 :
    exp (-((12369:ℝ)*ep12369)) ≤ scalar12369.upperTail ∧
    exp (-((12369:ℝ)*em12369)) ≤ scalar12369.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12369:ℝ)) (by norm_num [ep12369]) ?_)
      (show bp12369^8 ≤ scalar12369.upperTail by norm_num [bp12369, scalar12369])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12369, bp12369, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12369:ℝ)) (by norm_num [em12369]) ?_)
      (show bm12369^8 ≤ scalar12369.lowerTail by norm_num [bm12369, scalar12369])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12369, bm12369, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12369 :
    agent12369.root+dsL+scalar12369.worldRadius < √(1/100/aL) ∧
    2*(agent12369.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12369, agent12369, scalar12369, tp12369, tm12369, ep12369, em12369, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12369, agent12369, scalar12369, tp12369, tm12369, ep12369, em12369, dsL]

noncomputable def master12369 : MasterCertificate 12369 world12369 agent12369 :=
  master scalar12369 dsL tp12369 tm12369 ep12369 em12369
    (by norm_num [dsL]) (by norm_num [tp12369]) (by norm_num [tm12369])
    (by norm_num [ep12369]) (by norm_num [em12369])
    positive12369 negative12369 tails12369.1 tails12369.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12369.1 tailGuards12369.2

theorem preserves12369 : master12369.toScalarCertificate = scalar12369 := rfl

noncomputable def tp12370 : ℝ := (570993079 / 2500000000)
noncomputable def tm12370 : ℝ := (-((1198114821 / 2000000000)))
noncomputable def ep12370 : ℝ := (403579249537203 / 800000000000000000)
noncomputable def em12370 : ℝ := (12314070847685249 / 25000000000000000000)
noncomputable def bp12370 : ℝ := (45838629190675396739 / 100000000000000000000)
noncomputable def bm12370 : ℝ := (46690695456273805019 / 100000000000000000000)

theorem positive12370 :
    Eplus aL (agent12370.root+dsL) scalar12370.worldRadius world12370.frame
      agent12370.frame tp12370 ≤ -ep12370 := by
  apply positive_check (eT := (115484162798575888113 / 100000000000000000000)) (y := (1504153543663594631 / 4000000000000000000)) (u := (72825152095065467893 / 50000000000000000000))
  · norm_num [world12370, agent12370, scalar12370, tp12370, tm12370, ep12370, em12370, dsL]
  · norm_num [world12370, agent12370, scalar12370, tp12370, tm12370, ep12370, em12370, dsL]
  · norm_num [world12370, agent12370, scalar12370, tp12370, tm12370, ep12370, em12370, dsL]
  · norm_num [world12370, agent12370, scalar12370, tp12370, tm12370, ep12370, em12370, dsL]
  · norm_num [world12370, agent12370, scalar12370, tp12370, tm12370, ep12370, em12370, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12370, agent12370, tp12370, tm12370, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12370, agent12370, scalar12370, tp12370, tm12370, ep12370, em12370, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12370, agent12370, tp12370, tm12370, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12370, agent12370, scalar12370, tp12370, tm12370, ep12370, em12370, dsL]

theorem negative12370 :
    Eminus aL (agent12370.root+dsL) scalar12370.worldRadius world12370.frame
      agent12370.frame tm12370 ≤ -em12370 := by
  apply negative_check (lo := (3427531691841700297 / 5000000000000000000)) (hi := (68550633836834005941 / 100000000000000000000))
    (y := (-((71705075630554703837 / 100000000000000000000)))) (u := (48818992595913663771 / 100000000000000000000))
  · norm_num [world12370, agent12370, scalar12370, tp12370, tm12370, ep12370, em12370, dsL]
  · norm_num [world12370, agent12370, scalar12370, tp12370, tm12370, ep12370, em12370, dsL]
  · norm_num [world12370, agent12370, scalar12370, tp12370, tm12370, ep12370, em12370, dsL]
  · norm_num [world12370, agent12370, scalar12370, tp12370, tm12370, ep12370, em12370, dsL]
  · norm_num [world12370, agent12370, scalar12370, tp12370, tm12370, ep12370, em12370, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12370, agent12370, tp12370, tm12370, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12370, agent12370, tp12370, tm12370, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12370, agent12370, scalar12370, tp12370, tm12370, ep12370, em12370, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12370, agent12370, tp12370, tm12370, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12370, agent12370, scalar12370, tp12370, tm12370, ep12370, em12370, dsL]

theorem tails12370 :
    exp (-((12370:ℝ)*ep12370)) ≤ scalar12370.upperTail ∧
    exp (-((12370:ℝ)*em12370)) ≤ scalar12370.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12370:ℝ)) (by norm_num [ep12370]) ?_)
      (show bp12370^8 ≤ scalar12370.upperTail by norm_num [bp12370, scalar12370])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12370, bp12370, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12370:ℝ)) (by norm_num [em12370]) ?_)
      (show bm12370^8 ≤ scalar12370.lowerTail by norm_num [bm12370, scalar12370])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12370, bm12370, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12370 :
    agent12370.root+dsL+scalar12370.worldRadius < √(1/100/aL) ∧
    2*(agent12370.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12370, agent12370, scalar12370, tp12370, tm12370, ep12370, em12370, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12370, agent12370, scalar12370, tp12370, tm12370, ep12370, em12370, dsL]

noncomputable def master12370 : MasterCertificate 12370 world12370 agent12370 :=
  master scalar12370 dsL tp12370 tm12370 ep12370 em12370
    (by norm_num [dsL]) (by norm_num [tp12370]) (by norm_num [tm12370])
    (by norm_num [ep12370]) (by norm_num [em12370])
    positive12370 negative12370 tails12370.1 tails12370.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12370.1 tailGuards12370.2

theorem preserves12370 : master12370.toScalarCertificate = scalar12370 := rfl

noncomputable def tp12371 : ℝ := (1142034833 / 5000000000)
noncomputable def tm12371 : ℝ := (-((2995392697 / 5000000000)))
noncomputable def ep12371 : ℝ := (3153152258533481 / 6250000000000000000)
noncomputable def em12371 : ℝ := (6157363490089543 / 12500000000000000000)
noncomputable def bp12371 : ℝ := (1833343647224917171 / 4000000000000000000)
noncomputable def bm12371 : ℝ := (46685925991836550997 / 100000000000000000000)

theorem positive12371 :
    Eplus aL (agent12371.root+dsL) scalar12371.worldRadius world12371.frame
      agent12371.frame tp12371 ≤ -ep12371 := by
  apply positive_check (eT := (11548448612676463857 / 10000000000000000000)) (y := (18802377494440884171 / 50000000000000000000)) (u := (72825819465844970203 / 50000000000000000000))
  · norm_num [world12371, agent12371, scalar12371, tp12371, tm12371, ep12371, em12371, dsL]
  · norm_num [world12371, agent12371, scalar12371, tp12371, tm12371, ep12371, em12371, dsL]
  · norm_num [world12371, agent12371, scalar12371, tp12371, tm12371, ep12371, em12371, dsL]
  · norm_num [world12371, agent12371, scalar12371, tp12371, tm12371, ep12371, em12371, dsL]
  · norm_num [world12371, agent12371, scalar12371, tp12371, tm12371, ep12371, em12371, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12371, agent12371, tp12371, tm12371, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12371, agent12371, scalar12371, tp12371, tm12371, ep12371, em12371, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12371, agent12371, tp12371, tm12371, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12371, agent12371, scalar12371, tp12371, tm12371, ep12371, em12371, dsL]

theorem negative12371 :
    Eminus aL (agent12371.root+dsL) scalar12371.worldRadius world12371.frame
      agent12371.frame tm12371 ≤ -em12371 := by
  apply negative_check (lo := (68550320762943881837 / 100000000000000000000)) (hi := (34275160381471940919 / 50000000000000000000))
    (y := (-((35852640492785816299 / 50000000000000000000)))) (u := (6102361542970761303 / 12500000000000000000))
  · norm_num [world12371, agent12371, scalar12371, tp12371, tm12371, ep12371, em12371, dsL]
  · norm_num [world12371, agent12371, scalar12371, tp12371, tm12371, ep12371, em12371, dsL]
  · norm_num [world12371, agent12371, scalar12371, tp12371, tm12371, ep12371, em12371, dsL]
  · norm_num [world12371, agent12371, scalar12371, tp12371, tm12371, ep12371, em12371, dsL]
  · norm_num [world12371, agent12371, scalar12371, tp12371, tm12371, ep12371, em12371, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12371, agent12371, tp12371, tm12371, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12371, agent12371, tp12371, tm12371, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12371, agent12371, scalar12371, tp12371, tm12371, ep12371, em12371, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12371, agent12371, tp12371, tm12371, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12371, agent12371, scalar12371, tp12371, tm12371, ep12371, em12371, dsL]

theorem tails12371 :
    exp (-((12371:ℝ)*ep12371)) ≤ scalar12371.upperTail ∧
    exp (-((12371:ℝ)*em12371)) ≤ scalar12371.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12371:ℝ)) (by norm_num [ep12371]) ?_)
      (show bp12371^8 ≤ scalar12371.upperTail by norm_num [bp12371, scalar12371])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12371, bp12371, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12371:ℝ)) (by norm_num [em12371]) ?_)
      (show bm12371^8 ≤ scalar12371.lowerTail by norm_num [bm12371, scalar12371])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12371, bm12371, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12371 :
    agent12371.root+dsL+scalar12371.worldRadius < √(1/100/aL) ∧
    2*(agent12371.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12371, agent12371, scalar12371, tp12371, tm12371, ep12371, em12371, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12371, agent12371, scalar12371, tp12371, tm12371, ep12371, em12371, dsL]

noncomputable def master12371 : MasterCertificate 12371 world12371 agent12371 :=
  master scalar12371 dsL tp12371 tm12371 ep12371 em12371
    (by norm_num [dsL]) (by norm_num [tp12371]) (by norm_num [tm12371])
    (by norm_num [ep12371]) (by norm_num [em12371])
    positive12371 negative12371 tails12371.1 tails12371.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12371.1 tailGuards12371.2

theorem preserves12371 : master12371.toScalarCertificate = scalar12371 := rfl

noncomputable def tp12372 : ℝ := (2284166929 / 10000000000)
noncomputable def tm12372 : ℝ := (-((299549831 / 500000000)))
noncomputable def ep12372 : ℝ := (50453464974335437 / 100000000000000000000)
noncomputable def em12372 : ℝ := (49261531413159237 / 100000000000000000000)
noncomputable def bp12372 : ℝ := (2291427708071031399 / 5000000000000000000)
noncomputable def bm12372 : ℝ := (46681157457330539361 / 100000000000000000000)

theorem positive12372 :
    Eplus aL (agent12372.root+dsL) scalar12372.worldRadius world12372.frame
      agent12372.frame tp12372 ≤ -ep12372 := by
  apply positive_check (eT := (57742404426780242653 / 50000000000000000000)) (y := (4700708792643714533 / 12500000000000000000)) (u := (7282648608168603943 / 5000000000000000000))
  · norm_num [world12372, agent12372, scalar12372, tp12372, tm12372, ep12372, em12372, dsL]
  · norm_num [world12372, agent12372, scalar12372, tp12372, tm12372, ep12372, em12372, dsL]
  · norm_num [world12372, agent12372, scalar12372, tp12372, tm12372, ep12372, em12372, dsL]
  · norm_num [world12372, agent12372, scalar12372, tp12372, tm12372, ep12372, em12372, dsL]
  · norm_num [world12372, agent12372, scalar12372, tp12372, tm12372, ep12372, em12372, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12372, agent12372, tp12372, tm12372, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12372, agent12372, scalar12372, tp12372, tm12372, ep12372, em12372, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12372, agent12372, tp12372, tm12372, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12372, agent12372, scalar12372, tp12372, tm12372, ep12372, em12372, dsL]

theorem negative12372 :
    Eminus aL (agent12372.root+dsL) scalar12372.worldRadius world12372.frame
      agent12372.frame tm12372 ≤ -em12372 := by
  apply negative_check (lo := (17137501976413411471 / 25000000000000000000)) (hi := (13710001581130729177 / 20000000000000000000))
    (y := (-((71705486840349668743 / 100000000000000000000)))) (u := (48818791847847054321 / 100000000000000000000))
  · norm_num [world12372, agent12372, scalar12372, tp12372, tm12372, ep12372, em12372, dsL]
  · norm_num [world12372, agent12372, scalar12372, tp12372, tm12372, ep12372, em12372, dsL]
  · norm_num [world12372, agent12372, scalar12372, tp12372, tm12372, ep12372, em12372, dsL]
  · norm_num [world12372, agent12372, scalar12372, tp12372, tm12372, ep12372, em12372, dsL]
  · norm_num [world12372, agent12372, scalar12372, tp12372, tm12372, ep12372, em12372, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12372, agent12372, tp12372, tm12372, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12372, agent12372, tp12372, tm12372, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12372, agent12372, scalar12372, tp12372, tm12372, ep12372, em12372, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12372, agent12372, tp12372, tm12372, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12372, agent12372, scalar12372, tp12372, tm12372, ep12372, em12372, dsL]

theorem tails12372 :
    exp (-((12372:ℝ)*ep12372)) ≤ scalar12372.upperTail ∧
    exp (-((12372:ℝ)*em12372)) ≤ scalar12372.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12372:ℝ)) (by norm_num [ep12372]) ?_)
      (show bp12372^8 ≤ scalar12372.upperTail by norm_num [bp12372, scalar12372])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12372, bp12372, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12372:ℝ)) (by norm_num [em12372]) ?_)
      (show bm12372^8 ≤ scalar12372.lowerTail by norm_num [bm12372, scalar12372])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12372, bm12372, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12372 :
    agent12372.root+dsL+scalar12372.worldRadius < √(1/100/aL) ∧
    2*(agent12372.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12372, agent12372, scalar12372, tp12372, tm12372, ep12372, em12372, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12372, agent12372, scalar12372, tp12372, tm12372, ep12372, em12372, dsL]

noncomputable def master12372 : MasterCertificate 12372 world12372 agent12372 :=
  master scalar12372 dsL tp12372 tm12372 ep12372 em12372
    (by norm_num [dsL]) (by norm_num [tp12372]) (by norm_num [tm12372])
    (by norm_num [ep12372]) (by norm_num [em12372])
    positive12372 negative12372 tails12372.1 tails12372.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12372.1 tailGuards12372.2

theorem preserves12372 : master12372.toScalarCertificate = scalar12372 := rfl

noncomputable def tp12373 : ℝ := (2284264137 / 10000000000)
noncomputable def tm12373 : ℝ := (-((2995603839 / 5000000000)))
noncomputable def ep12373 : ℝ := (50456491906403787 / 100000000000000000000)
noncomputable def em12373 : ℝ := (49264153146994521 / 100000000000000000000)
noncomputable def bp12373 : ℝ := (916470373988453651 / 2000000000000000000)
noncomputable def bm12373 : ℝ := (23338195186651193329 / 50000000000000000000)

theorem positive12373 :
    Eplus aL (agent12373.root+dsL) scalar12373.worldRadius world12373.frame
      agent12373.frame tp12373 ≤ -ep12373 := by
  apply positive_check (eT := (28871282802982609459 / 25000000000000000000)) (y := (470082314495478827 / 1250000000000000000)) (u := (145654304629785425341 / 100000000000000000000))
  · norm_num [world12373, agent12373, scalar12373, tp12373, tm12373, ep12373, em12373, dsL]
  · norm_num [world12373, agent12373, scalar12373, tp12373, tm12373, ep12373, em12373, dsL]
  · norm_num [world12373, agent12373, scalar12373, tp12373, tm12373, ep12373, em12373, dsL]
  · norm_num [world12373, agent12373, scalar12373, tp12373, tm12373, ep12373, em12373, dsL]
  · norm_num [world12373, agent12373, scalar12373, tp12373, tm12373, ep12373, em12373, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12373, agent12373, tp12373, tm12373, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12373, agent12373, scalar12373, tp12373, tm12373, ep12373, em12373, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12373, agent12373, tp12373, tm12373, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12373, agent12373, scalar12373, tp12373, tm12373, ep12373, em12373, dsL]

theorem negative12373 :
    Eminus aL (agent12373.root+dsL) scalar12373.worldRadius world12373.frame
      agent12373.frame tm12373 ≤ -em12373 := by
  apply negative_check (lo := (68549695718585541573 / 100000000000000000000)) (hi := (34274847859292770787 / 50000000000000000000))
    (y := (-((35852845807269424703 / 50000000000000000000)))) (u := (48818691879664234649 / 100000000000000000000))
  · norm_num [world12373, agent12373, scalar12373, tp12373, tm12373, ep12373, em12373, dsL]
  · norm_num [world12373, agent12373, scalar12373, tp12373, tm12373, ep12373, em12373, dsL]
  · norm_num [world12373, agent12373, scalar12373, tp12373, tm12373, ep12373, em12373, dsL]
  · norm_num [world12373, agent12373, scalar12373, tp12373, tm12373, ep12373, em12373, dsL]
  · norm_num [world12373, agent12373, scalar12373, tp12373, tm12373, ep12373, em12373, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12373, agent12373, tp12373, tm12373, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12373, agent12373, tp12373, tm12373, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12373, agent12373, scalar12373, tp12373, tm12373, ep12373, em12373, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12373, agent12373, tp12373, tm12373, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12373, agent12373, scalar12373, tp12373, tm12373, ep12373, em12373, dsL]

theorem tails12373 :
    exp (-((12373:ℝ)*ep12373)) ≤ scalar12373.upperTail ∧
    exp (-((12373:ℝ)*em12373)) ≤ scalar12373.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12373:ℝ)) (by norm_num [ep12373]) ?_)
      (show bp12373^8 ≤ scalar12373.upperTail by norm_num [bp12373, scalar12373])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12373, bp12373, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12373:ℝ)) (by norm_num [em12373]) ?_)
      (show bm12373^8 ≤ scalar12373.lowerTail by norm_num [bm12373, scalar12373])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12373, bm12373, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12373 :
    agent12373.root+dsL+scalar12373.worldRadius < √(1/100/aL) ∧
    2*(agent12373.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12373, agent12373, scalar12373, tp12373, tm12373, ep12373, em12373, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12373, agent12373, scalar12373, tp12373, tm12373, ep12373, em12373, dsL]

noncomputable def master12373 : MasterCertificate 12373 world12373 agent12373 :=
  master scalar12373 dsL tp12373 tm12373 ep12373 em12373
    (by norm_num [dsL]) (by norm_num [tp12373]) (by norm_num [tm12373])
    (by norm_num [ep12373]) (by norm_num [em12373])
    positive12373 negative12373 tails12373.1 tails12373.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12373.1 tailGuards12373.2

theorem preserves12373 : master12373.toScalarCertificate = scalar12373 := rfl

noncomputable def tp12374 : ℝ := (2284361369 / 10000000000)
noncomputable def tm12374 : ℝ := (-((5991418521 / 10000000000)))
noncomputable def ep12374 : ℝ := (25229758400399711 / 50000000000000000000)
noncomputable def em12374 : ℝ := (49266772988591699 / 100000000000000000000)
noncomputable def bp12374 : ℝ := (45818484888071344569 / 100000000000000000000)
noncomputable def bm12374 : ℝ := (46671624836181948619 / 100000000000000000000)

theorem positive12374 :
    Eplus aL (agent12374.root+dsL) scalar12374.worldRadius world12374.frame
      agent12374.frame tp12374 ≤ -ep12374 := by
  apply positive_check (eT := (28871363444222561177 / 25000000000000000000)) (y := (18803750546867510519 / 50000000000000000000)) (u := (72827819366667303911 / 50000000000000000000))
  · norm_num [world12374, agent12374, scalar12374, tp12374, tm12374, ep12374, em12374, dsL]
  · norm_num [world12374, agent12374, scalar12374, tp12374, tm12374, ep12374, em12374, dsL]
  · norm_num [world12374, agent12374, scalar12374, tp12374, tm12374, ep12374, em12374, dsL]
  · norm_num [world12374, agent12374, scalar12374, tp12374, tm12374, ep12374, em12374, dsL]
  · norm_num [world12374, agent12374, scalar12374, tp12374, tm12374, ep12374, em12374, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12374, agent12374, tp12374, tm12374, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12374, agent12374, scalar12374, tp12374, tm12374, ep12374, em12374, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12374, agent12374, tp12374, tm12374, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12374, agent12374, scalar12374, tp12374, tm12374, ep12374, em12374, dsL]

theorem negative12374 :
    Eminus aL (agent12374.root+dsL) scalar12374.worldRadius world12374.frame
      agent12374.frame tm12374 ≤ -em12374 := by
  apply negative_check (lo := (34274692202384686257 / 50000000000000000000)) (hi := (13709876880953874503 / 20000000000000000000))
    (y := (-((71705895547123002901 / 100000000000000000000)))) (u := (24409296161272924627 / 50000000000000000000))
  · norm_num [world12374, agent12374, scalar12374, tp12374, tm12374, ep12374, em12374, dsL]
  · norm_num [world12374, agent12374, scalar12374, tp12374, tm12374, ep12374, em12374, dsL]
  · norm_num [world12374, agent12374, scalar12374, tp12374, tm12374, ep12374, em12374, dsL]
  · norm_num [world12374, agent12374, scalar12374, tp12374, tm12374, ep12374, em12374, dsL]
  · norm_num [world12374, agent12374, scalar12374, tp12374, tm12374, ep12374, em12374, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12374, agent12374, tp12374, tm12374, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12374, agent12374, tp12374, tm12374, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12374, agent12374, scalar12374, tp12374, tm12374, ep12374, em12374, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12374, agent12374, tp12374, tm12374, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12374, agent12374, scalar12374, tp12374, tm12374, ep12374, em12374, dsL]

theorem tails12374 :
    exp (-((12374:ℝ)*ep12374)) ≤ scalar12374.upperTail ∧
    exp (-((12374:ℝ)*em12374)) ≤ scalar12374.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12374:ℝ)) (by norm_num [ep12374]) ?_)
      (show bp12374^8 ≤ scalar12374.upperTail by norm_num [bp12374, scalar12374])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12374, bp12374, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12374:ℝ)) (by norm_num [em12374]) ?_)
      (show bm12374^8 ≤ scalar12374.lowerTail by norm_num [bm12374, scalar12374])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12374, bm12374, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12374 :
    agent12374.root+dsL+scalar12374.worldRadius < √(1/100/aL) ∧
    2*(agent12374.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12374, agent12374, scalar12374, tp12374, tm12374, ep12374, em12374, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12374, agent12374, scalar12374, tp12374, tm12374, ep12374, em12374, dsL]

noncomputable def master12374 : MasterCertificate 12374 world12374 agent12374 :=
  master scalar12374 dsL tp12374 tm12374 ep12374 em12374
    (by norm_num [dsL]) (by norm_num [tp12374]) (by norm_num [tm12374])
    (by norm_num [ep12374]) (by norm_num [em12374])
    positive12374 negative12374 tails12374.1 tails12374.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12374.1 tailGuards12374.2

theorem preserves12374 : master12374.toScalarCertificate = scalar12374 := rfl

end BstLean.Part268
