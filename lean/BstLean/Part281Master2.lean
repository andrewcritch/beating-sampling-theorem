import BstLean.Part261Checker
import BstLean.Part281Scalar2
namespace BstLean.Part281
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp11909 : ℝ := (1207792491 / 5000000000)
noncomputable def tm11909 : ℝ := (-((1249316139 / 2000000000)))
noncomputable def ep11909 : ℝ := (55970962615833687 / 100000000000000000000)
noncomputable def em11909 : ℝ := (53910761374394813 / 100000000000000000000)
noncomputable def bp11909 : ℝ := (10866428503714071607 / 25000000000000000000)
noncomputable def bm11909 : ℝ := (44819401482454902267 / 100000000000000000000)

theorem positive11909 :
    Eplus aL (agent11909.root+dsL) scalar11909.worldRadius world11909.frame
      agent11909.frame tp11909 ≤ -ep11909 := by
  apply positive_check (eT := (116643320591323763751 / 100000000000000000000)) (y := (24833424314317421 / 62500000000000000)) (u := (74392698193124963957 / 50000000000000000000))
  · norm_num [world11909, agent11909, scalar11909, tp11909, tm11909, ep11909, em11909, dsL]
  · norm_num [world11909, agent11909, scalar11909, tp11909, tm11909, ep11909, em11909, dsL]
  · norm_num [world11909, agent11909, scalar11909, tp11909, tm11909, ep11909, em11909, dsL]
  · norm_num [world11909, agent11909, scalar11909, tp11909, tm11909, ep11909, em11909, dsL]
  · norm_num [world11909, agent11909, scalar11909, tp11909, tm11909, ep11909, em11909, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11909, agent11909, tp11909, tm11909, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11909, agent11909, scalar11909, tp11909, tm11909, ep11909, em11909, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11909, agent11909, tp11909, tm11909, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11909, agent11909, scalar11909, tp11909, tm11909, ep11909, em11909, dsL]

theorem negative11909 :
    Eminus aL (agent11909.root+dsL) scalar11909.worldRadius world11909.frame
      agent11909.frame tm11909 ≤ -em11909 := by
  apply negative_check (lo := (13431785219415059613 / 20000000000000000000)) (hi := (33579463048537649033 / 50000000000000000000))
    (y := (-((4555121184895756187 / 6250000000000000000)))) (u := (48247827284824713973 / 100000000000000000000))
  · norm_num [world11909, agent11909, scalar11909, tp11909, tm11909, ep11909, em11909, dsL]
  · norm_num [world11909, agent11909, scalar11909, tp11909, tm11909, ep11909, em11909, dsL]
  · norm_num [world11909, agent11909, scalar11909, tp11909, tm11909, ep11909, em11909, dsL]
  · norm_num [world11909, agent11909, scalar11909, tp11909, tm11909, ep11909, em11909, dsL]
  · norm_num [world11909, agent11909, scalar11909, tp11909, tm11909, ep11909, em11909, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11909, agent11909, tp11909, tm11909, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11909, agent11909, tp11909, tm11909, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11909, agent11909, scalar11909, tp11909, tm11909, ep11909, em11909, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11909, agent11909, tp11909, tm11909, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11909, agent11909, scalar11909, tp11909, tm11909, ep11909, em11909, dsL]

theorem tails11909 :
    exp (-((11909:ℝ)*ep11909)) ≤ scalar11909.upperTail ∧
    exp (-((11909:ℝ)*em11909)) ≤ scalar11909.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11909:ℝ)) (by norm_num [ep11909]) ?_)
      (show bp11909^8 ≤ scalar11909.upperTail by norm_num [bp11909, scalar11909])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11909, bp11909, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11909:ℝ)) (by norm_num [em11909]) ?_)
      (show bm11909^8 ≤ scalar11909.lowerTail by norm_num [bm11909, scalar11909])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11909, bm11909, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11909 :
    agent11909.root+dsL+scalar11909.worldRadius < √(1/100/aL) ∧
    2*(agent11909.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11909, agent11909, scalar11909, tp11909, tm11909, ep11909, em11909, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11909, agent11909, scalar11909, tp11909, tm11909, ep11909, em11909, dsL]

noncomputable def master11909 : MasterCertificate 11909 world11909 agent11909 :=
  master scalar11909 dsL tp11909 tm11909 ep11909 em11909
    (by norm_num [dsL]) (by norm_num [tp11909]) (by norm_num [tm11909])
    (by norm_num [ep11909]) (by norm_num [em11909])
    positive11909 negative11909 tails11909.1 tails11909.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11909.1 tailGuards11909.2

theorem preserves11909 : master11909.toScalarCertificate = scalar11909 := rfl

noncomputable def tp11910 : ℝ := (2415682589 / 10000000000)
noncomputable def tm11910 : ℝ := (-((6246797329 / 10000000000)))
noncomputable def ep11910 : ℝ := (27986922156826047 / 50000000000000000000)
noncomputable def em11910 : ℝ := (6739156170669753 / 12500000000000000000)
noncomputable def bp11910 : ℝ := (43460808534766912869 / 100000000000000000000)
noncomputable def bm11910 : ℝ := (8962944261534976923 / 20000000000000000000)

theorem positive11910 :
    Eplus aL (agent11910.root+dsL) scalar11910.worldRadius world11910.frame
      agent11910.frame tp11910 ≤ -ep11910 := by
  apply positive_check (eT := (116643601141642103507 / 100000000000000000000)) (y := (9933531805245461541 / 25000000000000000000)) (u := (148786360991992985003 / 100000000000000000000))
  · norm_num [world11910, agent11910, scalar11910, tp11910, tm11910, ep11910, em11910, dsL]
  · norm_num [world11910, agent11910, scalar11910, tp11910, tm11910, ep11910, em11910, dsL]
  · norm_num [world11910, agent11910, scalar11910, tp11910, tm11910, ep11910, em11910, dsL]
  · norm_num [world11910, agent11910, scalar11910, tp11910, tm11910, ep11910, em11910, dsL]
  · norm_num [world11910, agent11910, scalar11910, tp11910, tm11910, ep11910, em11910, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11910, agent11910, tp11910, tm11910, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11910, agent11910, scalar11910, tp11910, tm11910, ep11910, em11910, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11910, agent11910, tp11910, tm11910, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11910, agent11910, scalar11910, tp11910, tm11910, ep11910, em11910, dsL]

theorem negative11910 :
    Eminus aL (agent11910.root+dsL) scalar11910.worldRadius world11910.frame
      agent11910.frame tm11910 ≤ -em11910 := by
  apply negative_check (lo := (33579330749308811969 / 50000000000000000000)) (hi := (67158661498617623939 / 100000000000000000000))
    (y := (-((72881575405839930607 / 100000000000000000000)))) (u := (12062000672830518051 / 25000000000000000000))
  · norm_num [world11910, agent11910, scalar11910, tp11910, tm11910, ep11910, em11910, dsL]
  · norm_num [world11910, agent11910, scalar11910, tp11910, tm11910, ep11910, em11910, dsL]
  · norm_num [world11910, agent11910, scalar11910, tp11910, tm11910, ep11910, em11910, dsL]
  · norm_num [world11910, agent11910, scalar11910, tp11910, tm11910, ep11910, em11910, dsL]
  · norm_num [world11910, agent11910, scalar11910, tp11910, tm11910, ep11910, em11910, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11910, agent11910, tp11910, tm11910, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11910, agent11910, tp11910, tm11910, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11910, agent11910, scalar11910, tp11910, tm11910, ep11910, em11910, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11910, agent11910, tp11910, tm11910, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11910, agent11910, scalar11910, tp11910, tm11910, ep11910, em11910, dsL]

theorem tails11910 :
    exp (-((11910:ℝ)*ep11910)) ≤ scalar11910.upperTail ∧
    exp (-((11910:ℝ)*em11910)) ≤ scalar11910.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11910:ℝ)) (by norm_num [ep11910]) ?_)
      (show bp11910^8 ≤ scalar11910.upperTail by norm_num [bp11910, scalar11910])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11910, bp11910, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11910:ℝ)) (by norm_num [em11910]) ?_)
      (show bm11910^8 ≤ scalar11910.lowerTail by norm_num [bm11910, scalar11910])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11910, bm11910, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11910 :
    agent11910.root+dsL+scalar11910.worldRadius < √(1/100/aL) ∧
    2*(agent11910.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11910, agent11910, scalar11910, tp11910, tm11910, ep11910, em11910, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11910, agent11910, scalar11910, tp11910, tm11910, ep11910, em11910, dsL]

noncomputable def master11910 : MasterCertificate 11910 world11910 agent11910 :=
  master scalar11910 dsL tp11910 tm11910 ep11910 em11910
    (by norm_num [dsL]) (by norm_num [tp11910]) (by norm_num [tm11910])
    (by norm_num [ep11910]) (by norm_num [em11910])
    positive11910 negative11910 tails11910.1 tails11910.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11910.1 tailGuards11910.2

theorem preserves11910 : master11910.toScalarCertificate = scalar11910 := rfl

noncomputable def tp11911 : ℝ := (2415780089 / 10000000000)
noncomputable def tm11911 : ℝ := (-((249880557 / 400000000)))
noncomputable def ep11911 : ℝ := (27988362154394899 / 50000000000000000000)
noncomputable def em11911 : ℝ := (53915735783110967 / 100000000000000000000)
noncomputable def bp11911 : ℝ := (43455904396877626801 / 100000000000000000000)
noncomputable def bm11911 : ℝ := (4481004239248677939 / 10000000000000000000)

theorem positive11911 :
    Eplus aL (agent11911.root+dsL) scalar11911.worldRadius world11911.frame
      agent11911.frame tp11911 ≤ -ep11911 := by
  apply positive_check (eT := (11664388093848356347 / 10000000000000000000)) (y := (39734774218130522469 / 100000000000000000000)) (u := (148787323638620367189 / 100000000000000000000))
  · norm_num [world11911, agent11911, scalar11911, tp11911, tm11911, ep11911, em11911, dsL]
  · norm_num [world11911, agent11911, scalar11911, tp11911, tm11911, ep11911, em11911, dsL]
  · norm_num [world11911, agent11911, scalar11911, tp11911, tm11911, ep11911, em11911, dsL]
  · norm_num [world11911, agent11911, scalar11911, tp11911, tm11911, ep11911, em11911, dsL]
  · norm_num [world11911, agent11911, scalar11911, tp11911, tm11911, ep11911, em11911, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11911, agent11911, tp11911, tm11911, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11911, agent11911, scalar11911, tp11911, tm11911, ep11911, em11911, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11911, agent11911, tp11911, tm11911, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11911, agent11911, scalar11911, tp11911, tm11911, ep11911, em11911, dsL]

theorem negative11911 :
    Eminus aL (agent11911.root+dsL) scalar11911.worldRadius world11911.frame
      agent11911.frame tm11911 ≤ -em11911 := by
  apply negative_check (lo := (33579198497422656473 / 50000000000000000000)) (hi := (67158396994845312947 / 100000000000000000000))
    (y := (-((36440606257936395431 / 50000000000000000000)))) (u := (48248177778800871581 / 100000000000000000000))
  · norm_num [world11911, agent11911, scalar11911, tp11911, tm11911, ep11911, em11911, dsL]
  · norm_num [world11911, agent11911, scalar11911, tp11911, tm11911, ep11911, em11911, dsL]
  · norm_num [world11911, agent11911, scalar11911, tp11911, tm11911, ep11911, em11911, dsL]
  · norm_num [world11911, agent11911, scalar11911, tp11911, tm11911, ep11911, em11911, dsL]
  · norm_num [world11911, agent11911, scalar11911, tp11911, tm11911, ep11911, em11911, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11911, agent11911, tp11911, tm11911, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11911, agent11911, tp11911, tm11911, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11911, agent11911, scalar11911, tp11911, tm11911, ep11911, em11911, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11911, agent11911, tp11911, tm11911, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11911, agent11911, scalar11911, tp11911, tm11911, ep11911, em11911, dsL]

theorem tails11911 :
    exp (-((11911:ℝ)*ep11911)) ≤ scalar11911.upperTail ∧
    exp (-((11911:ℝ)*em11911)) ≤ scalar11911.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11911:ℝ)) (by norm_num [ep11911]) ?_)
      (show bp11911^8 ≤ scalar11911.upperTail by norm_num [bp11911, scalar11911])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11911, bp11911, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11911:ℝ)) (by norm_num [em11911]) ?_)
      (show bm11911^8 ≤ scalar11911.lowerTail by norm_num [bm11911, scalar11911])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11911, bm11911, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11911 :
    agent11911.root+dsL+scalar11911.worldRadius < √(1/100/aL) ∧
    2*(agent11911.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11911, agent11911, scalar11911, tp11911, tm11911, ep11911, em11911, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11911, agent11911, scalar11911, tp11911, tm11911, ep11911, em11911, dsL]

noncomputable def master11911 : MasterCertificate 11911 world11911 agent11911 :=
  master scalar11911 dsL tp11911 tm11911 ep11911 em11911
    (by norm_num [dsL]) (by norm_num [tp11911]) (by norm_num [tm11911])
    (by norm_num [ep11911]) (by norm_num [em11911])
    positive11911 negative11911 tails11911.1 tails11911.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11911.1 tailGuards11911.2

theorem preserves11911 : master11911.toScalarCertificate = scalar11911 := rfl

noncomputable def tp11912 : ℝ := (603969391 / 2500000000)
noncomputable def tm11912 : ℝ := (-((1561807611 / 2500000000)))
noncomputable def ep11912 : ℝ := (55979602709885477 / 100000000000000000000)
noncomputable def em11912 : ℝ := (53918220756967221 / 100000000000000000000)
noncomputable def bp11912 : ℝ := (43451001530848794429 / 100000000000000000000)
noncomputable def bm11912 : ℝ := (44805364650590635713 / 100000000000000000000)

theorem positive11912 :
    Eplus aL (agent11912.root+dsL) scalar11912.worldRadius world11912.frame
      agent11912.frame tp11912 ≤ -ep11912 := by
  apply positive_check (eT := (7290260036965812343 / 6250000000000000000)) (y := (9933855323987739001 / 25000000000000000000)) (u := (148788286411506190907 / 100000000000000000000))
  · norm_num [world11912, agent11912, scalar11912, tp11912, tm11912, ep11912, em11912, dsL]
  · norm_num [world11912, agent11912, scalar11912, tp11912, tm11912, ep11912, em11912, dsL]
  · norm_num [world11912, agent11912, scalar11912, tp11912, tm11912, ep11912, em11912, dsL]
  · norm_num [world11912, agent11912, scalar11912, tp11912, tm11912, ep11912, em11912, dsL]
  · norm_num [world11912, agent11912, scalar11912, tp11912, tm11912, ep11912, em11912, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11912, agent11912, tp11912, tm11912, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11912, agent11912, scalar11912, tp11912, tm11912, ep11912, em11912, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11912, agent11912, tp11912, tm11912, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11912, agent11912, scalar11912, tp11912, tm11912, ep11912, em11912, dsL]

theorem negative11912 :
    Eminus aL (agent11912.root+dsL) scalar11912.worldRadius world11912.frame
      agent11912.frame tm11912 ≤ -em11912 := by
  apply negative_check (lo := (4197383297040380663 / 6250000000000000000)) (hi := (67158132752646090609 / 100000000000000000000))
    (y := (-((72880850041293357927 / 100000000000000000000)))) (u := (24124176333248660437 / 50000000000000000000))
  · norm_num [world11912, agent11912, scalar11912, tp11912, tm11912, ep11912, em11912, dsL]
  · norm_num [world11912, agent11912, scalar11912, tp11912, tm11912, ep11912, em11912, dsL]
  · norm_num [world11912, agent11912, scalar11912, tp11912, tm11912, ep11912, em11912, dsL]
  · norm_num [world11912, agent11912, scalar11912, tp11912, tm11912, ep11912, em11912, dsL]
  · norm_num [world11912, agent11912, scalar11912, tp11912, tm11912, ep11912, em11912, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11912, agent11912, tp11912, tm11912, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11912, agent11912, tp11912, tm11912, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11912, agent11912, scalar11912, tp11912, tm11912, ep11912, em11912, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11912, agent11912, tp11912, tm11912, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11912, agent11912, scalar11912, tp11912, tm11912, ep11912, em11912, dsL]

theorem tails11912 :
    exp (-((11912:ℝ)*ep11912)) ≤ scalar11912.upperTail ∧
    exp (-((11912:ℝ)*em11912)) ≤ scalar11912.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11912:ℝ)) (by norm_num [ep11912]) ?_)
      (show bp11912^8 ≤ scalar11912.upperTail by norm_num [bp11912, scalar11912])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11912, bp11912, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11912:ℝ)) (by norm_num [em11912]) ?_)
      (show bm11912^8 ≤ scalar11912.lowerTail by norm_num [bm11912, scalar11912])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11912, bm11912, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11912 :
    agent11912.root+dsL+scalar11912.worldRadius < √(1/100/aL) ∧
    2*(agent11912.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11912, agent11912, scalar11912, tp11912, tm11912, ep11912, em11912, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11912, agent11912, scalar11912, tp11912, tm11912, ep11912, em11912, dsL]

noncomputable def master11912 : MasterCertificate 11912 world11912 agent11912 :=
  master scalar11912 dsL tp11912 tm11912 ep11912 em11912
    (by norm_num [dsL]) (by norm_num [tp11912]) (by norm_num [tm11912])
    (by norm_num [ep11912]) (by norm_num [em11912])
    positive11912 negative11912 tails11912.1 tails11912.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11912.1 tailGuards11912.2

theorem preserves11912 : master11912.toScalarCertificate = scalar11912 := rfl

noncomputable def tp11913 : ℝ := (1207987507 / 5000000000)
noncomputable def tm11913 : ℝ := (-((6247446889 / 10000000000)))
noncomputable def ep11913 : ℝ := (1399561970301191 / 2500000000000000000)
noncomputable def em11913 : ℝ := (53920703579353799 / 100000000000000000000)
noncomputable def bp11913 : ℝ := (5430762549084480393 / 12500000000000000000)
noncomputable def bm11913 : ℝ := (358405508432100623 / 800000000000000000)

theorem positive11913 :
    Eplus aL (agent11913.root+dsL) scalar11913.worldRadius world11913.frame
      agent11913.frame tp11913 ≤ -ep11913 := by
  apply positive_check (eT := (29161110025136086401 / 25000000000000000000)) (y := (397360686130971177 / 1000000000000000000)) (u := (148789249546712879063 / 100000000000000000000))
  · norm_num [world11913, agent11913, scalar11913, tp11913, tm11913, ep11913, em11913, dsL]
  · norm_num [world11913, agent11913, scalar11913, tp11913, tm11913, ep11913, em11913, dsL]
  · norm_num [world11913, agent11913, scalar11913, tp11913, tm11913, ep11913, em11913, dsL]
  · norm_num [world11913, agent11913, scalar11913, tp11913, tm11913, ep11913, em11913, dsL]
  · norm_num [world11913, agent11913, scalar11913, tp11913, tm11913, ep11913, em11913, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11913, agent11913, tp11913, tm11913, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11913, agent11913, scalar11913, tp11913, tm11913, ep11913, em11913, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11913, agent11913, tp11913, tm11913, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11913, agent11913, scalar11913, tp11913, tm11913, ep11913, em11913, dsL]

theorem negative11913 :
    Eminus aL (agent11913.root+dsL) scalar11913.worldRadius world11913.frame
      agent11913.frame tm11913 ≤ -em11913 := by
  apply negative_check (lo := (67157868759183302691 / 100000000000000000000)) (hi := (16789467189795825673 / 25000000000000000000))
    (y := (-((36440243817224309493 / 50000000000000000000)))) (u := (48248527522146702273 / 100000000000000000000))
  · norm_num [world11913, agent11913, scalar11913, tp11913, tm11913, ep11913, em11913, dsL]
  · norm_num [world11913, agent11913, scalar11913, tp11913, tm11913, ep11913, em11913, dsL]
  · norm_num [world11913, agent11913, scalar11913, tp11913, tm11913, ep11913, em11913, dsL]
  · norm_num [world11913, agent11913, scalar11913, tp11913, tm11913, ep11913, em11913, dsL]
  · norm_num [world11913, agent11913, scalar11913, tp11913, tm11913, ep11913, em11913, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11913, agent11913, tp11913, tm11913, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11913, agent11913, tp11913, tm11913, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11913, agent11913, scalar11913, tp11913, tm11913, ep11913, em11913, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11913, agent11913, tp11913, tm11913, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11913, agent11913, scalar11913, tp11913, tm11913, ep11913, em11913, dsL]

theorem tails11913 :
    exp (-((11913:ℝ)*ep11913)) ≤ scalar11913.upperTail ∧
    exp (-((11913:ℝ)*em11913)) ≤ scalar11913.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11913:ℝ)) (by norm_num [ep11913]) ?_)
      (show bp11913^8 ≤ scalar11913.upperTail by norm_num [bp11913, scalar11913])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11913, bp11913, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11913:ℝ)) (by norm_num [em11913]) ?_)
      (show bm11913^8 ≤ scalar11913.lowerTail by norm_num [bm11913, scalar11913])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11913, bm11913, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11913 :
    agent11913.root+dsL+scalar11913.worldRadius < √(1/100/aL) ∧
    2*(agent11913.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11913, agent11913, scalar11913, tp11913, tm11913, ep11913, em11913, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11913, agent11913, scalar11913, tp11913, tm11913, ep11913, em11913, dsL]

noncomputable def master11913 : MasterCertificate 11913 world11913 agent11913 :=
  master scalar11913 dsL tp11913 tm11913 ep11913 em11913
    (by norm_num [dsL]) (by norm_num [tp11913]) (by norm_num [tm11913])
    (by norm_num [ep11913]) (by norm_num [em11913])
    positive11913 negative11913 tails11913.1 tails11913.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11913.1 tailGuards11913.2

theorem preserves11913 : master11913.toScalarCertificate = scalar11913 := rfl

noncomputable def tp11914 : ℝ := (483214471 / 2000000000)
noncomputable def tm11914 : ℝ := (-((6247663117 / 10000000000)))
noncomputable def ep11914 : ℝ := (55985353704540471 / 100000000000000000000)
noncomputable def em11914 : ℝ := (539231852824077 / 1000000000000000000)
noncomputable def bp11914 : ℝ := (10860300069393997751 / 25000000000000000000)
noncomputable def bm11914 : ℝ := (11199003353534193797 / 25000000000000000000)

theorem positive11914 :
    Eplus aL (agent11914.root+dsL) scalar11914.worldRadius world11914.frame
      agent11914.frame tp11914 ≤ -ep11914 := by
  apply positive_check (eT := (58322359420699494193 / 50000000000000000000)) (y := (39736714521092474869 / 100000000000000000000)) (u := (148790210591475662351 / 100000000000000000000))
  · norm_num [world11914, agent11914, scalar11914, tp11914, tm11914, ep11914, em11914, dsL]
  · norm_num [world11914, agent11914, scalar11914, tp11914, tm11914, ep11914, em11914, dsL]
  · norm_num [world11914, agent11914, scalar11914, tp11914, tm11914, ep11914, em11914, dsL]
  · norm_num [world11914, agent11914, scalar11914, tp11914, tm11914, ep11914, em11914, dsL]
  · norm_num [world11914, agent11914, scalar11914, tp11914, tm11914, ep11914, em11914, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11914, agent11914, tp11914, tm11914, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11914, agent11914, scalar11914, tp11914, tm11914, ep11914, em11914, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11914, agent11914, tp11914, tm11914, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11914, agent11914, scalar11914, tp11914, tm11914, ep11914, em11914, dsL]

theorem negative11914 :
    Eminus aL (agent11914.root+dsL) scalar11914.worldRadius world11914.frame
      agent11914.frame tm11914 ≤ -em11914 := by
  apply negative_check (lo := (67157605626397325253 / 100000000000000000000)) (hi := (33578802813198662627 / 50000000000000000000))
    (y := (-((72880124316468724963 / 100000000000000000000)))) (u := (24124351409020332453 / 50000000000000000000))
  · norm_num [world11914, agent11914, scalar11914, tp11914, tm11914, ep11914, em11914, dsL]
  · norm_num [world11914, agent11914, scalar11914, tp11914, tm11914, ep11914, em11914, dsL]
  · norm_num [world11914, agent11914, scalar11914, tp11914, tm11914, ep11914, em11914, dsL]
  · norm_num [world11914, agent11914, scalar11914, tp11914, tm11914, ep11914, em11914, dsL]
  · norm_num [world11914, agent11914, scalar11914, tp11914, tm11914, ep11914, em11914, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11914, agent11914, tp11914, tm11914, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11914, agent11914, tp11914, tm11914, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11914, agent11914, scalar11914, tp11914, tm11914, ep11914, em11914, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11914, agent11914, tp11914, tm11914, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11914, agent11914, scalar11914, tp11914, tm11914, ep11914, em11914, dsL]

theorem tails11914 :
    exp (-((11914:ℝ)*ep11914)) ≤ scalar11914.upperTail ∧
    exp (-((11914:ℝ)*em11914)) ≤ scalar11914.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11914:ℝ)) (by norm_num [ep11914]) ?_)
      (show bp11914^8 ≤ scalar11914.upperTail by norm_num [bp11914, scalar11914])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11914, bp11914, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11914:ℝ)) (by norm_num [em11914]) ?_)
      (show bm11914^8 ≤ scalar11914.lowerTail by norm_num [bm11914, scalar11914])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11914, bm11914, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11914 :
    agent11914.root+dsL+scalar11914.worldRadius < √(1/100/aL) ∧
    2*(agent11914.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11914, agent11914, scalar11914, tp11914, tm11914, ep11914, em11914, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11914, agent11914, scalar11914, tp11914, tm11914, ep11914, em11914, dsL]

noncomputable def master11914 : MasterCertificate 11914 world11914 agent11914 :=
  master scalar11914 dsL tp11914 tm11914 ep11914 em11914
    (by norm_num [dsL]) (by norm_num [tp11914]) (by norm_num [tm11914])
    (by norm_num [ep11914]) (by norm_num [em11914])
    positive11914 negative11914 tails11914.1 tails11914.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11914.1 tailGuards11914.2

theorem preserves11914 : master11914.toScalarCertificate = scalar11914 := rfl

noncomputable def tp11915 : ℝ := (2416169629 / 10000000000)
noncomputable def tm11915 : ℝ := (-((6247879321 / 10000000000)))
noncomputable def ep11915 : ℝ := (27994113504087103 / 50000000000000000000)
noncomputable def em11915 : ℝ := (53925665546134757 / 100000000000000000000)
noncomputable def bp11915 : ℝ := (21718150715416910123 / 50000000000000000000)
noncomputable def bm11915 : ℝ := (44791339444425212127 / 100000000000000000000)

theorem positive11915 :
    Eplus aL (agent11915.root+dsL) scalar11915.worldRadius world11915.frame
      agent11915.frame tp11915 ≤ -ep11915 := by
  apply positive_check (eT := (29161249281551990229 / 25000000000000000000)) (y := (6208962463084969 / 15625000000000000)) (u := (148791170652472755601 / 100000000000000000000))
  · norm_num [world11915, agent11915, scalar11915, tp11915, tm11915, ep11915, em11915, dsL]
  · norm_num [world11915, agent11915, scalar11915, tp11915, tm11915, ep11915, em11915, dsL]
  · norm_num [world11915, agent11915, scalar11915, tp11915, tm11915, ep11915, em11915, dsL]
  · norm_num [world11915, agent11915, scalar11915, tp11915, tm11915, ep11915, em11915, dsL]
  · norm_num [world11915, agent11915, scalar11915, tp11915, tm11915, ep11915, em11915, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11915, agent11915, tp11915, tm11915, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11915, agent11915, scalar11915, tp11915, tm11915, ep11915, em11915, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11915, agent11915, tp11915, tm11915, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11915, agent11915, scalar11915, tp11915, tm11915, ep11915, em11915, dsL]

theorem negative11915 :
    Eminus aL (agent11915.root+dsL) scalar11915.worldRadius world11915.frame
      agent11915.frame tm11915 ≤ -em11915 := by
  apply negative_check (lo := (8394667816043416849 / 12500000000000000000)) (hi := (67157342528347334793 / 100000000000000000000))
    (y := (-((72879761915812011523 / 100000000000000000000)))) (u := (4824887767197336891 / 10000000000000000000))
  · norm_num [world11915, agent11915, scalar11915, tp11915, tm11915, ep11915, em11915, dsL]
  · norm_num [world11915, agent11915, scalar11915, tp11915, tm11915, ep11915, em11915, dsL]
  · norm_num [world11915, agent11915, scalar11915, tp11915, tm11915, ep11915, em11915, dsL]
  · norm_num [world11915, agent11915, scalar11915, tp11915, tm11915, ep11915, em11915, dsL]
  · norm_num [world11915, agent11915, scalar11915, tp11915, tm11915, ep11915, em11915, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11915, agent11915, tp11915, tm11915, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11915, agent11915, tp11915, tm11915, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11915, agent11915, scalar11915, tp11915, tm11915, ep11915, em11915, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11915, agent11915, tp11915, tm11915, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11915, agent11915, scalar11915, tp11915, tm11915, ep11915, em11915, dsL]

theorem tails11915 :
    exp (-((11915:ℝ)*ep11915)) ≤ scalar11915.upperTail ∧
    exp (-((11915:ℝ)*em11915)) ≤ scalar11915.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11915:ℝ)) (by norm_num [ep11915]) ?_)
      (show bp11915^8 ≤ scalar11915.upperTail by norm_num [bp11915, scalar11915])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11915, bp11915, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11915:ℝ)) (by norm_num [em11915]) ?_)
      (show bm11915^8 ≤ scalar11915.lowerTail by norm_num [bm11915, scalar11915])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11915, bm11915, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11915 :
    agent11915.root+dsL+scalar11915.worldRadius < √(1/100/aL) ∧
    2*(agent11915.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11915, agent11915, scalar11915, tp11915, tm11915, ep11915, em11915, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11915, agent11915, scalar11915, tp11915, tm11915, ep11915, em11915, dsL]

noncomputable def master11915 : MasterCertificate 11915 world11915 agent11915 :=
  master scalar11915 dsL tp11915 tm11915 ep11915 em11915
    (by norm_num [dsL]) (by norm_num [tp11915]) (by norm_num [tm11915])
    (by norm_num [ep11915]) (by norm_num [em11915])
    positive11915 negative11915 tails11915.1 tails11915.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11915.1 tailGuards11915.2

theorem preserves11915 : master11915.toScalarCertificate = scalar11915 := rfl

noncomputable def tp11916 : ℝ := (1208133473 / 5000000000)
noncomputable def tm11916 : ℝ := (-((1562023843 / 2500000000)))
noncomputable def ep11916 : ℝ := (27995549252947321 / 50000000000000000000)
noncomputable def em11916 : ℝ := (53928144112266253 / 100000000000000000000)
noncomputable def bp11916 : ℝ := (43431403992818346429 / 100000000000000000000)
noncomputable def bm11916 : ℝ := (8957333363429106537 / 20000000000000000000)

theorem positive11916 :
    Eplus aL (agent11916.root+dsL) scalar11916.worldRadius world11916.frame
      agent11916.frame tp11916 ≤ -ep11916 := by
  apply positive_check (eT := (58322637886323668987 / 50000000000000000000)) (y := (19869003199777828549 / 50000000000000000000)) (u := (29758426558515568281 / 20000000000000000000))
  · norm_num [world11916, agent11916, scalar11916, tp11916, tm11916, ep11916, em11916, dsL]
  · norm_num [world11916, agent11916, scalar11916, tp11916, tm11916, ep11916, em11916, dsL]
  · norm_num [world11916, agent11916, scalar11916, tp11916, tm11916, ep11916, em11916, dsL]
  · norm_num [world11916, agent11916, scalar11916, tp11916, tm11916, ep11916, em11916, dsL]
  · norm_num [world11916, agent11916, scalar11916, tp11916, tm11916, ep11916, em11916, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11916, agent11916, tp11916, tm11916, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11916, agent11916, scalar11916, tp11916, tm11916, ep11916, em11916, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11916, agent11916, tp11916, tm11916, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11916, agent11916, scalar11916, tp11916, tm11916, ep11916, em11916, dsL]

theorem negative11916 :
    Eminus aL (agent11916.root+dsL) scalar11916.worldRadius world11916.frame
      agent11916.frame tm11916 ≤ -em11916 := by
  apply negative_check (lo := (6715708001700453173 / 10000000000000000000)) (hi := (67157080017004531731 / 100000000000000000000))
    (y := (-((36439699479556180617 / 50000000000000000000)))) (u := (48249052794825195279 / 100000000000000000000))
  · norm_num [world11916, agent11916, scalar11916, tp11916, tm11916, ep11916, em11916, dsL]
  · norm_num [world11916, agent11916, scalar11916, tp11916, tm11916, ep11916, em11916, dsL]
  · norm_num [world11916, agent11916, scalar11916, tp11916, tm11916, ep11916, em11916, dsL]
  · norm_num [world11916, agent11916, scalar11916, tp11916, tm11916, ep11916, em11916, dsL]
  · norm_num [world11916, agent11916, scalar11916, tp11916, tm11916, ep11916, em11916, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11916, agent11916, tp11916, tm11916, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11916, agent11916, tp11916, tm11916, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11916, agent11916, scalar11916, tp11916, tm11916, ep11916, em11916, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11916, agent11916, tp11916, tm11916, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11916, agent11916, scalar11916, tp11916, tm11916, ep11916, em11916, dsL]

theorem tails11916 :
    exp (-((11916:ℝ)*ep11916)) ≤ scalar11916.upperTail ∧
    exp (-((11916:ℝ)*em11916)) ≤ scalar11916.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11916:ℝ)) (by norm_num [ep11916]) ?_)
      (show bp11916^8 ≤ scalar11916.upperTail by norm_num [bp11916, scalar11916])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11916, bp11916, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11916:ℝ)) (by norm_num [em11916]) ?_)
      (show bm11916^8 ≤ scalar11916.lowerTail by norm_num [bm11916, scalar11916])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11916, bm11916, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11916 :
    agent11916.root+dsL+scalar11916.worldRadius < √(1/100/aL) ∧
    2*(agent11916.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11916, agent11916, scalar11916, tp11916, tm11916, ep11916, em11916, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11916, agent11916, scalar11916, tp11916, tm11916, ep11916, em11916, dsL]

noncomputable def master11916 : MasterCertificate 11916 world11916 agent11916 :=
  master scalar11916 dsL tp11916 tm11916 ep11916 em11916
    (by norm_num [dsL]) (by norm_num [tp11916]) (by norm_num [tm11916])
    (by norm_num [ep11916]) (by norm_num [em11916])
    positive11916 negative11916 tails11916.1 tails11916.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11916.1 tailGuards11916.2

theorem preserves11916 : master11916.toScalarCertificate = scalar11916 := rfl

noncomputable def tp11917 : ℝ := (2416364149 / 10000000000)
noncomputable def tm11917 : ℝ := (-((624831119 / 1000000000)))
noncomputable def ep11917 : ℝ := (27996983986740503 / 50000000000000000000)
noncomputable def em11917 : ℝ := (2696531041061883 / 5000000000000000000)
noncomputable def bp11917 : ℝ := (4342650810851837583 / 10000000000000000000)
noncomputable def bm11917 : ℝ := (22390997819353671397 / 50000000000000000000)

theorem positive11917 :
    Eplus aL (agent11917.root+dsL) scalar11917.worldRadius world11917.frame
      agent11917.frame tp11917 ≤ -ep11917 := by
  apply positive_check (eT := (58322776806850871239 / 50000000000000000000)) (y := (19869325740100868177 / 50000000000000000000)) (u := (18599136578115652237 / 12500000000000000000))
  · norm_num [world11917, agent11917, scalar11917, tp11917, tm11917, ep11917, em11917, dsL]
  · norm_num [world11917, agent11917, scalar11917, tp11917, tm11917, ep11917, em11917, dsL]
  · norm_num [world11917, agent11917, scalar11917, tp11917, tm11917, ep11917, em11917, dsL]
  · norm_num [world11917, agent11917, scalar11917, tp11917, tm11917, ep11917, em11917, dsL]
  · norm_num [world11917, agent11917, scalar11917, tp11917, tm11917, ep11917, em11917, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11917, agent11917, tp11917, tm11917, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11917, agent11917, scalar11917, tp11917, tm11917, ep11917, em11917, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11917, agent11917, tp11917, tm11917, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11917, agent11917, scalar11917, tp11917, tm11917, ep11917, em11917, dsL]

theorem negative11917 :
    Eminus aL (agent11917.root+dsL) scalar11917.worldRadius world11917.frame
      agent11917.frame tm11917 ≤ -em11917 := by
  apply negative_check (lo := (16789204608690920737 / 25000000000000000000)) (hi := (67156818434763682949 / 100000000000000000000))
    (y := (-((36439517193699023623 / 50000000000000000000)))) (u := (2412461434877237761 / 5000000000000000000))
  · norm_num [world11917, agent11917, scalar11917, tp11917, tm11917, ep11917, em11917, dsL]
  · norm_num [world11917, agent11917, scalar11917, tp11917, tm11917, ep11917, em11917, dsL]
  · norm_num [world11917, agent11917, scalar11917, tp11917, tm11917, ep11917, em11917, dsL]
  · norm_num [world11917, agent11917, scalar11917, tp11917, tm11917, ep11917, em11917, dsL]
  · norm_num [world11917, agent11917, scalar11917, tp11917, tm11917, ep11917, em11917, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11917, agent11917, tp11917, tm11917, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11917, agent11917, tp11917, tm11917, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11917, agent11917, scalar11917, tp11917, tm11917, ep11917, em11917, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11917, agent11917, tp11917, tm11917, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11917, agent11917, scalar11917, tp11917, tm11917, ep11917, em11917, dsL]

theorem tails11917 :
    exp (-((11917:ℝ)*ep11917)) ≤ scalar11917.upperTail ∧
    exp (-((11917:ℝ)*em11917)) ≤ scalar11917.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11917:ℝ)) (by norm_num [ep11917]) ?_)
      (show bp11917^8 ≤ scalar11917.upperTail by norm_num [bp11917, scalar11917])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11917, bp11917, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11917:ℝ)) (by norm_num [em11917]) ?_)
      (show bm11917^8 ≤ scalar11917.lowerTail by norm_num [bm11917, scalar11917])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11917, bm11917, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11917 :
    agent11917.root+dsL+scalar11917.worldRadius < √(1/100/aL) ∧
    2*(agent11917.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11917, agent11917, scalar11917, tp11917, tm11917, ep11917, em11917, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11917, agent11917, scalar11917, tp11917, tm11917, ep11917, em11917, dsL]

noncomputable def master11917 : MasterCertificate 11917 world11917 agent11917 :=
  master scalar11917 dsL tp11917 tm11917 ep11917 em11917
    (by norm_num [dsL]) (by norm_num [tp11917]) (by norm_num [tm11917])
    (by norm_num [ep11917]) (by norm_num [em11917])
    positive11917 negative11917 tails11917.1 tails11917.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11917.1 tailGuards11917.2

theorem preserves11917 : master11917.toScalarCertificate = scalar11917 := rfl

noncomputable def tp11918 : ℝ := (1208230643 / 5000000000)
noncomputable def tm11918 : ℝ := (-((78106587 / 125000000)))
noncomputable def ep11918 : ℝ := (55996836236769829 / 100000000000000000000)
noncomputable def em11918 : ℝ := (53933096415667759 / 100000000000000000000)
noncomputable def bp11918 : ℝ := (21710806621825881929 / 50000000000000000000)
noncomputable def bm11918 : ℝ := (44777325413691955971 / 100000000000000000000)

theorem positive11918 :
    Eplus aL (agent11918.root+dsL) scalar11918.worldRadius world11918.frame
      agent11918.frame tp11918 ≤ -ep11918 := by
  apply positive_check (eT := (2916145775154867727 / 2500000000000000000)) (y := (2483705994616470203 / 6250000000000000000)) (u := (37198512875197540693 / 25000000000000000000))
  · norm_num [world11918, agent11918, scalar11918, tp11918, tm11918, ep11918, em11918, dsL]
  · norm_num [world11918, agent11918, scalar11918, tp11918, tm11918, ep11918, em11918, dsL]
  · norm_num [world11918, agent11918, scalar11918, tp11918, tm11918, ep11918, em11918, dsL]
  · norm_num [world11918, agent11918, scalar11918, tp11918, tm11918, ep11918, em11918, dsL]
  · norm_num [world11918, agent11918, scalar11918, tp11918, tm11918, ep11918, em11918, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11918, agent11918, tp11918, tm11918, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11918, agent11918, scalar11918, tp11918, tm11918, ep11918, em11918, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11918, agent11918, tp11918, tm11918, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11918, agent11918, scalar11918, tp11918, tm11918, ep11918, em11918, dsL]

theorem negative11918 :
    Eminus aL (agent11918.root+dsL) scalar11918.worldRadius world11918.frame
      agent11918.frame tm11918 ≤ -em11918 := by
  apply negative_check (lo := (67156556989897951001 / 100000000000000000000)) (hi := (33578278494948975501 / 50000000000000000000))
    (y := (-((72878670507716547053 / 100000000000000000000)))) (u := (24124702133501948373 / 50000000000000000000))
  · norm_num [world11918, agent11918, scalar11918, tp11918, tm11918, ep11918, em11918, dsL]
  · norm_num [world11918, agent11918, scalar11918, tp11918, tm11918, ep11918, em11918, dsL]
  · norm_num [world11918, agent11918, scalar11918, tp11918, tm11918, ep11918, em11918, dsL]
  · norm_num [world11918, agent11918, scalar11918, tp11918, tm11918, ep11918, em11918, dsL]
  · norm_num [world11918, agent11918, scalar11918, tp11918, tm11918, ep11918, em11918, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11918, agent11918, tp11918, tm11918, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11918, agent11918, tp11918, tm11918, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11918, agent11918, scalar11918, tp11918, tm11918, ep11918, em11918, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11918, agent11918, tp11918, tm11918, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11918, agent11918, scalar11918, tp11918, tm11918, ep11918, em11918, dsL]

theorem tails11918 :
    exp (-((11918:ℝ)*ep11918)) ≤ scalar11918.upperTail ∧
    exp (-((11918:ℝ)*em11918)) ≤ scalar11918.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11918:ℝ)) (by norm_num [ep11918]) ?_)
      (show bp11918^8 ≤ scalar11918.upperTail by norm_num [bp11918, scalar11918])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11918, bp11918, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11918:ℝ)) (by norm_num [em11918]) ?_)
      (show bm11918^8 ≤ scalar11918.lowerTail by norm_num [bm11918, scalar11918])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11918, bm11918, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11918 :
    agent11918.root+dsL+scalar11918.worldRadius < √(1/100/aL) ∧
    2*(agent11918.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11918, agent11918, scalar11918, tp11918, tm11918, ep11918, em11918, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11918, agent11918, scalar11918, tp11918, tm11918, ep11918, em11918, dsL]

noncomputable def master11918 : MasterCertificate 11918 world11918 agent11918 :=
  master scalar11918 dsL tp11918 tm11918 ep11918 em11918
    (by norm_num [dsL]) (by norm_num [tp11918]) (by norm_num [tm11918])
    (by norm_num [ep11918]) (by norm_num [em11918])
    positive11918 negative11918 tails11918.1 tails11918.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11918.1 tailGuards11918.2

theorem preserves11918 : master11918.toScalarCertificate = scalar11918 := rfl

noncomputable def tp11919 : ℝ := (2416558391 / 10000000000)
noncomputable def tm11919 : ℝ := (-((3124371311 / 5000000000)))
noncomputable def ep11919 : ℝ := (55999702906699533 / 100000000000000000000)
noncomputable def em11919 : ℝ := (26967785283619027 / 50000000000000000000)
noncomputable def bp11919 : ℝ := (43416719649860644073 / 100000000000000000000)
noncomputable def bm11919 : ℝ := (44772656361096845323 / 100000000000000000000)

theorem positive11919 :
    Eplus aL (agent11919.root+dsL) scalar11919.worldRadius world11919.frame
      agent11919.frame tp11919 ≤ -ep11919 := by
  apply positive_check (eT := (116646108202894209633 / 100000000000000000000)) (y := (9934985075564932221 / 25000000000000000000)) (u := (14879501031548152009 / 10000000000000000000))
  · norm_num [world11919, agent11919, scalar11919, tp11919, tm11919, ep11919, em11919, dsL]
  · norm_num [world11919, agent11919, scalar11919, tp11919, tm11919, ep11919, em11919, dsL]
  · norm_num [world11919, agent11919, scalar11919, tp11919, tm11919, ep11919, em11919, dsL]
  · norm_num [world11919, agent11919, scalar11919, tp11919, tm11919, ep11919, em11919, dsL]
  · norm_num [world11919, agent11919, scalar11919, tp11919, tm11919, ep11919, em11919, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11919, agent11919, tp11919, tm11919, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11919, agent11919, scalar11919, tp11919, tm11919, ep11919, em11919, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11919, agent11919, tp11919, tm11919, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11919, agent11919, scalar11919, tp11919, tm11919, ep11919, em11919, dsL]

theorem negative11919 :
    Eminus aL (agent11919.root+dsL) scalar11919.worldRadius world11919.frame
      agent11919.frame tm11919 ≤ -em11919 := by
  apply negative_check (lo := (67156295939074156833 / 100000000000000000000)) (hi := (33578147969537078417 / 50000000000000000000))
    (y := (-((72878306745674588147 / 100000000000000000000)))) (u := (48249579780341316663 / 100000000000000000000))
  · norm_num [world11919, agent11919, scalar11919, tp11919, tm11919, ep11919, em11919, dsL]
  · norm_num [world11919, agent11919, scalar11919, tp11919, tm11919, ep11919, em11919, dsL]
  · norm_num [world11919, agent11919, scalar11919, tp11919, tm11919, ep11919, em11919, dsL]
  · norm_num [world11919, agent11919, scalar11919, tp11919, tm11919, ep11919, em11919, dsL]
  · norm_num [world11919, agent11919, scalar11919, tp11919, tm11919, ep11919, em11919, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11919, agent11919, tp11919, tm11919, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11919, agent11919, tp11919, tm11919, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11919, agent11919, scalar11919, tp11919, tm11919, ep11919, em11919, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11919, agent11919, tp11919, tm11919, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11919, agent11919, scalar11919, tp11919, tm11919, ep11919, em11919, dsL]

theorem tails11919 :
    exp (-((11919:ℝ)*ep11919)) ≤ scalar11919.upperTail ∧
    exp (-((11919:ℝ)*em11919)) ≤ scalar11919.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11919:ℝ)) (by norm_num [ep11919]) ?_)
      (show bp11919^8 ≤ scalar11919.upperTail by norm_num [bp11919, scalar11919])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11919, bp11919, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11919:ℝ)) (by norm_num [em11919]) ?_)
      (show bm11919^8 ≤ scalar11919.lowerTail by norm_num [bm11919, scalar11919])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11919, bm11919, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11919 :
    agent11919.root+dsL+scalar11919.worldRadius < √(1/100/aL) ∧
    2*(agent11919.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11919, agent11919, scalar11919, tp11919, tm11919, ep11919, em11919, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11919, agent11919, scalar11919, tp11919, tm11919, ep11919, em11919, dsL]

noncomputable def master11919 : MasterCertificate 11919 world11919 agent11919 :=
  master scalar11919 dsL tp11919 tm11919 ep11919 em11919
    (by norm_num [dsL]) (by norm_num [tp11919]) (by norm_num [tm11919])
    (by norm_num [ep11919]) (by norm_num [em11919])
    positive11919 negative11919 tails11919.1 tails11919.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11919.1 tailGuards11919.2

theorem preserves11919 : master11919.toScalarCertificate = scalar11919 := rfl

noncomputable def tp11920 : ℝ := (2416655459 / 10000000000)
noncomputable def tm11920 : ℝ := (-((249958329 / 400000000)))
noncomputable def ep11920 : ℝ := (2800128389042939 / 5000000000000000000)
noncomputable def em11920 : ℝ := (3371127689374453 / 6250000000000000000)
noncomputable def bp11920 : ℝ := (43411827458025994273 / 100000000000000000000)
noncomputable def bm11920 : ℝ := (4476798864496314861 / 10000000000000000000)

theorem positive11920 :
    Eplus aL (agent11920.root+dsL) scalar11920.worldRadius world11920.frame
      agent11920.frame tp11920 ≤ -ep11920 := by
  apply positive_check (eT := (2916159629164517573 / 2500000000000000000)) (y := (39740584663300916689 / 100000000000000000000)) (u := (37198992273912056011 / 25000000000000000000))
  · norm_num [world11920, agent11920, scalar11920, tp11920, tm11920, ep11920, em11920, dsL]
  · norm_num [world11920, agent11920, scalar11920, tp11920, tm11920, ep11920, em11920, dsL]
  · norm_num [world11920, agent11920, scalar11920, tp11920, tm11920, ep11920, em11920, dsL]
  · norm_num [world11920, agent11920, scalar11920, tp11920, tm11920, ep11920, em11920, dsL]
  · norm_num [world11920, agent11920, scalar11920, tp11920, tm11920, ep11920, em11920, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11920, agent11920, tp11920, tm11920, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11920, agent11920, scalar11920, tp11920, tm11920, ep11920, em11920, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11920, agent11920, tp11920, tm11920, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11920, agent11920, scalar11920, tp11920, tm11920, ep11920, em11920, dsL]

theorem negative11920 :
    Eminus aL (agent11920.root+dsL) scalar11920.worldRadius world11920.frame
      agent11920.frame tm11920 ≤ -em11920 := by
  apply negative_check (lo := (2686241402908177311 / 4000000000000000000)) (hi := (8394504384088054097 / 12500000000000000000))
    (y := (-((72877943318510987259 / 100000000000000000000)))) (u := (9649951026547840127 / 20000000000000000000))
  · norm_num [world11920, agent11920, scalar11920, tp11920, tm11920, ep11920, em11920, dsL]
  · norm_num [world11920, agent11920, scalar11920, tp11920, tm11920, ep11920, em11920, dsL]
  · norm_num [world11920, agent11920, scalar11920, tp11920, tm11920, ep11920, em11920, dsL]
  · norm_num [world11920, agent11920, scalar11920, tp11920, tm11920, ep11920, em11920, dsL]
  · norm_num [world11920, agent11920, scalar11920, tp11920, tm11920, ep11920, em11920, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11920, agent11920, tp11920, tm11920, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11920, agent11920, tp11920, tm11920, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11920, agent11920, scalar11920, tp11920, tm11920, ep11920, em11920, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11920, agent11920, tp11920, tm11920, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11920, agent11920, scalar11920, tp11920, tm11920, ep11920, em11920, dsL]

theorem tails11920 :
    exp (-((11920:ℝ)*ep11920)) ≤ scalar11920.upperTail ∧
    exp (-((11920:ℝ)*em11920)) ≤ scalar11920.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11920:ℝ)) (by norm_num [ep11920]) ?_)
      (show bp11920^8 ≤ scalar11920.upperTail by norm_num [bp11920, scalar11920])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11920, bp11920, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11920:ℝ)) (by norm_num [em11920]) ?_)
      (show bm11920^8 ≤ scalar11920.lowerTail by norm_num [bm11920, scalar11920])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11920, bm11920, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11920 :
    agent11920.root+dsL+scalar11920.worldRadius < √(1/100/aL) ∧
    2*(agent11920.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11920, agent11920, scalar11920, tp11920, tm11920, ep11920, em11920, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11920, agent11920, scalar11920, tp11920, tm11920, ep11920, em11920, dsL]

noncomputable def master11920 : MasterCertificate 11920 world11920 agent11920 :=
  master scalar11920 dsL tp11920 tm11920 ep11920 em11920
    (by norm_num [dsL]) (by norm_num [tp11920]) (by norm_num [tm11920])
    (by norm_num [ep11920]) (by norm_num [em11920])
    positive11920 negative11920 tails11920.1 tails11920.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11920.1 tailGuards11920.2

theorem preserves11920 : master11920.toScalarCertificate = scalar11920 := rfl

noncomputable def tp11921 : ℝ := (2416752477 / 10000000000)
noncomputable def tm11921 : ℝ := (-((1249834701 / 2000000000)))
noncomputable def ep11921 : ℝ := (11201086094022061 / 20000000000000000000)
noncomputable def em11921 : ℝ := (6742564184440113 / 12500000000000000000)
noncomputable def bp11921 : ℝ := (21703468459895660311 / 50000000000000000000)
noncomputable def bm11921 : ℝ := (8952664496862926541 / 20000000000000000000)

theorem positive11921 :
    Eplus aL (agent11921.root+dsL) scalar11921.worldRadius world11921.frame
      agent11921.frame tp11921 ≤ -ep11921 := by
  apply positive_check (eT := (116646661800667006521 / 100000000000000000000)) (y := (19870614382371957637 / 50000000000000000000)) (u := (148796927495718823871 / 100000000000000000000))
  · norm_num [world11921, agent11921, scalar11921, tp11921, tm11921, ep11921, em11921, dsL]
  · norm_num [world11921, agent11921, scalar11921, tp11921, tm11921, ep11921, em11921, dsL]
  · norm_num [world11921, agent11921, scalar11921, tp11921, tm11921, ep11921, em11921, dsL]
  · norm_num [world11921, agent11921, scalar11921, tp11921, tm11921, ep11921, em11921, dsL]
  · norm_num [world11921, agent11921, scalar11921, tp11921, tm11921, ep11921, em11921, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11921, agent11921, tp11921, tm11921, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11921, agent11921, scalar11921, tp11921, tm11921, ep11921, em11921, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11921, agent11921, tp11921, tm11921, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11921, agent11921, scalar11921, tp11921, tm11921, ep11921, em11921, dsL]

theorem negative11921 :
    Eminus aL (agent11921.root+dsL) scalar11921.worldRadius world11921.frame
      agent11921.frame tm11921 ≤ -em11921 := by
  apply negative_check (lo := (8394471940042058139 / 12500000000000000000)) (hi := (67155775520336465113 / 100000000000000000000))
    (y := (-((36438788857575295017 / 50000000000000000000)))) (u := (48249931535787816903 / 100000000000000000000))
  · norm_num [world11921, agent11921, scalar11921, tp11921, tm11921, ep11921, em11921, dsL]
  · norm_num [world11921, agent11921, scalar11921, tp11921, tm11921, ep11921, em11921, dsL]
  · norm_num [world11921, agent11921, scalar11921, tp11921, tm11921, ep11921, em11921, dsL]
  · norm_num [world11921, agent11921, scalar11921, tp11921, tm11921, ep11921, em11921, dsL]
  · norm_num [world11921, agent11921, scalar11921, tp11921, tm11921, ep11921, em11921, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11921, agent11921, tp11921, tm11921, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11921, agent11921, tp11921, tm11921, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11921, agent11921, scalar11921, tp11921, tm11921, ep11921, em11921, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11921, agent11921, tp11921, tm11921, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11921, agent11921, scalar11921, tp11921, tm11921, ep11921, em11921, dsL]

theorem tails11921 :
    exp (-((11921:ℝ)*ep11921)) ≤ scalar11921.upperTail ∧
    exp (-((11921:ℝ)*em11921)) ≤ scalar11921.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11921:ℝ)) (by norm_num [ep11921]) ?_)
      (show bp11921^8 ≤ scalar11921.upperTail by norm_num [bp11921, scalar11921])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11921, bp11921, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11921:ℝ)) (by norm_num [em11921]) ?_)
      (show bm11921^8 ≤ scalar11921.lowerTail by norm_num [bm11921, scalar11921])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11921, bm11921, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11921 :
    agent11921.root+dsL+scalar11921.worldRadius < √(1/100/aL) ∧
    2*(agent11921.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11921, agent11921, scalar11921, tp11921, tm11921, ep11921, em11921, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11921, agent11921, scalar11921, tp11921, tm11921, ep11921, em11921, dsL]

noncomputable def master11921 : MasterCertificate 11921 world11921 agent11921 :=
  master scalar11921 dsL tp11921 tm11921 ep11921 em11921
    (by norm_num [dsL]) (by norm_num [tp11921]) (by norm_num [tm11921])
    (by norm_num [ep11921]) (by norm_num [em11921])
    positive11921 negative11921 tails11921.1 tails11921.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11921.1 tailGuards11921.2

theorem preserves11921 : master11921.toScalarCertificate = scalar11921 := rfl

noncomputable def tp11922 : ℝ := (37763273 / 156250000)
noncomputable def tm11922 : ℝ := (-((6249388891 / 10000000000)))
noncomputable def ep11922 : ℝ := (56008291960389669 / 100000000000000000000)
noncomputable def em11922 : ℝ := (53942982811259029 / 100000000000000000000)
noncomputable def bp11922 : ℝ := (2170102369868770717 / 5000000000000000000)
noncomputable def bm11922 : ℝ := (11189664318458338263 / 25000000000000000000)

theorem positive11922 :
    Eplus aL (agent11922.root+dsL) scalar11922.worldRadius world11922.frame
      agent11922.frame tp11922 ≤ -ep11922 := by
  apply positive_check (eT := (58323469152908665111 / 50000000000000000000)) (y := (39741872981197316363 / 100000000000000000000)) (u := (29759577214619111971 / 20000000000000000000))
  · norm_num [world11922, agent11922, scalar11922, tp11922, tm11922, ep11922, em11922, dsL]
  · norm_num [world11922, agent11922, scalar11922, tp11922, tm11922, ep11922, em11922, dsL]
  · norm_num [world11922, agent11922, scalar11922, tp11922, tm11922, ep11922, em11922, dsL]
  · norm_num [world11922, agent11922, scalar11922, tp11922, tm11922, ep11922, em11922, dsL]
  · norm_num [world11922, agent11922, scalar11922, tp11922, tm11922, ep11922, em11922, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11922, agent11922, tp11922, tm11922, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11922, agent11922, scalar11922, tp11922, tm11922, ep11922, em11922, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11922, agent11922, tp11922, tm11922, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11922, agent11922, scalar11922, tp11922, tm11922, ep11922, em11922, dsL]

theorem negative11922 :
    Eminus aL (agent11922.root+dsL) scalar11922.worldRadius world11922.frame
      agent11922.frame tm11922 ≤ -em11922 := by
  apply negative_check (lo := (16788878861591703741 / 25000000000000000000)) (hi := (13431103089273362993 / 20000000000000000000))
    (y := (-((36438607131986813727 / 50000000000000000000)))) (u := (1930004276042022029 / 4000000000000000000))
  · norm_num [world11922, agent11922, scalar11922, tp11922, tm11922, ep11922, em11922, dsL]
  · norm_num [world11922, agent11922, scalar11922, tp11922, tm11922, ep11922, em11922, dsL]
  · norm_num [world11922, agent11922, scalar11922, tp11922, tm11922, ep11922, em11922, dsL]
  · norm_num [world11922, agent11922, scalar11922, tp11922, tm11922, ep11922, em11922, dsL]
  · norm_num [world11922, agent11922, scalar11922, tp11922, tm11922, ep11922, em11922, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11922, agent11922, tp11922, tm11922, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11922, agent11922, tp11922, tm11922, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11922, agent11922, scalar11922, tp11922, tm11922, ep11922, em11922, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11922, agent11922, tp11922, tm11922, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11922, agent11922, scalar11922, tp11922, tm11922, ep11922, em11922, dsL]

theorem tails11922 :
    exp (-((11922:ℝ)*ep11922)) ≤ scalar11922.upperTail ∧
    exp (-((11922:ℝ)*em11922)) ≤ scalar11922.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11922:ℝ)) (by norm_num [ep11922]) ?_)
      (show bp11922^8 ≤ scalar11922.upperTail by norm_num [bp11922, scalar11922])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11922, bp11922, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11922:ℝ)) (by norm_num [em11922]) ?_)
      (show bm11922^8 ≤ scalar11922.lowerTail by norm_num [bm11922, scalar11922])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11922, bm11922, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11922 :
    agent11922.root+dsL+scalar11922.worldRadius < √(1/100/aL) ∧
    2*(agent11922.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11922, agent11922, scalar11922, tp11922, tm11922, ep11922, em11922, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11922, agent11922, scalar11922, tp11922, tm11922, ep11922, em11922, dsL]

noncomputable def master11922 : MasterCertificate 11922 world11922 agent11922 :=
  master scalar11922 dsL tp11922 tm11922 ep11922 em11922
    (by norm_num [dsL]) (by norm_num [tp11922]) (by norm_num [tm11922])
    (by norm_num [ep11922]) (by norm_num [em11922])
    positive11922 negative11922 tails11922.1 tails11922.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11922.1 tailGuards11922.2

theorem preserves11922 : master11922.toScalarCertificate = scalar11922 := rfl

noncomputable def tp11923 : ℝ := (75529573 / 312500000)
noncomputable def tm11923 : ℝ := (-((6249604071 / 10000000000)))
noncomputable def ep11923 : ℝ := (437587124327831 / 781250000000000000)
noncomputable def em11923 : ℝ := (13486362686066391 / 25000000000000000000)
noncomputable def bp11923 : ℝ := (43397159109194293073 / 100000000000000000000)
noncomputable def bm11923 : ℝ := (895079864178031113 / 2000000000000000000)

theorem positive11923 :
    Eplus aL (agent11923.root+dsL) scalar11923.worldRadius world11923.frame
      agent11923.frame tp11923 ≤ -ep11923 := by
  apply positive_check (eT := (116647213879439116843 / 100000000000000000000)) (y := (39742515287536311517 / 100000000000000000000)) (u := (37199710453604872101 / 25000000000000000000))
  · norm_num [world11923, agent11923, scalar11923, tp11923, tm11923, ep11923, em11923, dsL]
  · norm_num [world11923, agent11923, scalar11923, tp11923, tm11923, ep11923, em11923, dsL]
  · norm_num [world11923, agent11923, scalar11923, tp11923, tm11923, ep11923, em11923, dsL]
  · norm_num [world11923, agent11923, scalar11923, tp11923, tm11923, ep11923, em11923, dsL]
  · norm_num [world11923, agent11923, scalar11923, tp11923, tm11923, ep11923, em11923, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11923, agent11923, tp11923, tm11923, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11923, agent11923, scalar11923, tp11923, tm11923, ep11923, em11923, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11923, agent11923, tp11923, tm11923, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11923, agent11923, scalar11923, tp11923, tm11923, ep11923, em11923, dsL]

theorem negative11923 :
    Eminus aL (agent11923.root+dsL) scalar11923.worldRadius world11923.frame
      agent11923.frame tm11923 ≤ -em11923 := by
  apply negative_check (lo := (33577628092852844291 / 50000000000000000000)) (hi := (67155256185705688583 / 100000000000000000000))
    (y := (-((72876849579490717923 / 100000000000000000000)))) (u := (24125141431012128553 / 50000000000000000000))
  · norm_num [world11923, agent11923, scalar11923, tp11923, tm11923, ep11923, em11923, dsL]
  · norm_num [world11923, agent11923, scalar11923, tp11923, tm11923, ep11923, em11923, dsL]
  · norm_num [world11923, agent11923, scalar11923, tp11923, tm11923, ep11923, em11923, dsL]
  · norm_num [world11923, agent11923, scalar11923, tp11923, tm11923, ep11923, em11923, dsL]
  · norm_num [world11923, agent11923, scalar11923, tp11923, tm11923, ep11923, em11923, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11923, agent11923, tp11923, tm11923, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11923, agent11923, tp11923, tm11923, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11923, agent11923, scalar11923, tp11923, tm11923, ep11923, em11923, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11923, agent11923, tp11923, tm11923, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11923, agent11923, scalar11923, tp11923, tm11923, ep11923, em11923, dsL]

theorem tails11923 :
    exp (-((11923:ℝ)*ep11923)) ≤ scalar11923.upperTail ∧
    exp (-((11923:ℝ)*em11923)) ≤ scalar11923.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11923:ℝ)) (by norm_num [ep11923]) ?_)
      (show bp11923^8 ≤ scalar11923.upperTail by norm_num [bp11923, scalar11923])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11923, bp11923, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11923:ℝ)) (by norm_num [em11923]) ?_)
      (show bm11923^8 ≤ scalar11923.lowerTail by norm_num [bm11923, scalar11923])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11923, bm11923, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11923 :
    agent11923.root+dsL+scalar11923.worldRadius < √(1/100/aL) ∧
    2*(agent11923.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11923, agent11923, scalar11923, tp11923, tm11923, ep11923, em11923, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11923, agent11923, scalar11923, tp11923, tm11923, ep11923, em11923, dsL]

noncomputable def master11923 : MasterCertificate 11923 world11923 agent11923 :=
  master scalar11923 dsL tp11923 tm11923 ep11923 em11923
    (by norm_num [dsL]) (by norm_num [tp11923]) (by norm_num [tm11923])
    (by norm_num [ep11923]) (by norm_num [em11923])
    positive11923 negative11923 tails11923.1 tails11923.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11923.1 tailGuards11923.2

theorem preserves11923 : master11923.toScalarCertificate = scalar11923 := rfl

noncomputable def tp11924 : ℝ := (2417043337 / 10000000000)
noncomputable def tm11924 : ℝ := (-((3124909747 / 5000000000)))
noncomputable def ep11924 : ℝ := (28007005965167771 / 50000000000000000000)
noncomputable def em11924 : ℝ := (1685872470675097 / 3125000000000000000)
noncomputable def bp11924 : ℝ := (1084806775517622773 / 2500000000000000000)
noncomputable def bm11924 : ℝ := (22374664548773588939 / 50000000000000000000)

theorem positive11924 :
    Eplus aL (agent11924.root+dsL) scalar11924.worldRadius world11924.frame
      agent11924.frame tp11924 ≤ -ep11924 := by
  apply positive_check (eT := (58323745256602645269 / 50000000000000000000)) (y := (7948631583107615759 / 20000000000000000000)) (u := (148799798040515778297 / 100000000000000000000))
  · norm_num [world11924, agent11924, scalar11924, tp11924, tm11924, ep11924, em11924, dsL]
  · norm_num [world11924, agent11924, scalar11924, tp11924, tm11924, ep11924, em11924, dsL]
  · norm_num [world11924, agent11924, scalar11924, tp11924, tm11924, ep11924, em11924, dsL]
  · norm_num [world11924, agent11924, scalar11924, tp11924, tm11924, ep11924, em11924, dsL]
  · norm_num [world11924, agent11924, scalar11924, tp11924, tm11924, ep11924, em11924, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11924, agent11924, tp11924, tm11924, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11924, agent11924, scalar11924, tp11924, tm11924, ep11924, em11924, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11924, agent11924, tp11924, tm11924, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11924, agent11924, scalar11924, tp11924, tm11924, ep11924, em11924, dsL]

theorem negative11924 :
    Eminus aL (agent11924.root+dsL) scalar11924.worldRadius world11924.frame
      agent11924.frame tm11924 ≤ -em11924 := by
  apply negative_check (lo := (67154995817330720577 / 100000000000000000000)) (hi := (33577497908665360289 / 50000000000000000000))
    (y := (-((455478019203514147 / 625000000000000000)))) (u := (6031307462872251531 / 12500000000000000000))
  · norm_num [world11924, agent11924, scalar11924, tp11924, tm11924, ep11924, em11924, dsL]
  · norm_num [world11924, agent11924, scalar11924, tp11924, tm11924, ep11924, em11924, dsL]
  · norm_num [world11924, agent11924, scalar11924, tp11924, tm11924, ep11924, em11924, dsL]
  · norm_num [world11924, agent11924, scalar11924, tp11924, tm11924, ep11924, em11924, dsL]
  · norm_num [world11924, agent11924, scalar11924, tp11924, tm11924, ep11924, em11924, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11924, agent11924, tp11924, tm11924, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11924, agent11924, tp11924, tm11924, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11924, agent11924, scalar11924, tp11924, tm11924, ep11924, em11924, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11924, agent11924, tp11924, tm11924, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11924, agent11924, scalar11924, tp11924, tm11924, ep11924, em11924, dsL]

theorem tails11924 :
    exp (-((11924:ℝ)*ep11924)) ≤ scalar11924.upperTail ∧
    exp (-((11924:ℝ)*em11924)) ≤ scalar11924.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11924:ℝ)) (by norm_num [ep11924]) ?_)
      (show bp11924^8 ≤ scalar11924.upperTail by norm_num [bp11924, scalar11924])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11924, bp11924, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11924:ℝ)) (by norm_num [em11924]) ?_)
      (show bm11924^8 ≤ scalar11924.lowerTail by norm_num [bm11924, scalar11924])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11924, bm11924, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11924 :
    agent11924.root+dsL+scalar11924.worldRadius < √(1/100/aL) ∧
    2*(agent11924.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11924, agent11924, scalar11924, tp11924, tm11924, ep11924, em11924, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11924, agent11924, scalar11924, tp11924, tm11924, ep11924, em11924, dsL]

noncomputable def master11924 : MasterCertificate 11924 world11924 agent11924 :=
  master scalar11924 dsL tp11924 tm11924 ep11924 em11924
    (by norm_num [dsL]) (by norm_num [tp11924]) (by norm_num [tm11924])
    (by norm_num [ep11924]) (by norm_num [em11924])
    positive11924 negative11924 tails11924.1 tails11924.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11924.1 tailGuards11924.2

theorem preserves11924 : master11924.toScalarCertificate = scalar11924 := rfl

noncomputable def tp11925 : ℝ := (1208570257 / 5000000000)
noncomputable def tm11925 : ℝ := (-((6250035341 / 10000000000)))
noncomputable def ep11925 : ℝ := (56016874698881207 / 100000000000000000000)
noncomputable def em11925 : ℝ := (53950390624353759 / 100000000000000000000)
noncomputable def bp11925 : ℝ := (43387381392620628091 / 100000000000000000000)
noncomputable def bm11925 : ℝ := (11186165757887722883 / 25000000000000000000)

theorem positive11925 :
    Eplus aL (agent11925.root+dsL) scalar11925.worldRadius world11925.frame
      agent11925.frame tp11925 ≤ -ep11925 := by
  apply positive_check (eT := (5832388424842432759 / 5000000000000000000)) (y := (39743797746534504717 / 100000000000000000000)) (u := (148800750110792077809 / 100000000000000000000))
  · norm_num [world11925, agent11925, scalar11925, tp11925, tm11925, ep11925, em11925, dsL]
  · norm_num [world11925, agent11925, scalar11925, tp11925, tm11925, ep11925, em11925, dsL]
  · norm_num [world11925, agent11925, scalar11925, tp11925, tm11925, ep11925, em11925, dsL]
  · norm_num [world11925, agent11925, scalar11925, tp11925, tm11925, ep11925, em11925, dsL]
  · norm_num [world11925, agent11925, scalar11925, tp11925, tm11925, ep11925, em11925, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11925, agent11925, tp11925, tm11925, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11925, agent11925, scalar11925, tp11925, tm11925, ep11925, em11925, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11925, agent11925, tp11925, tm11925, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11925, agent11925, scalar11925, tp11925, tm11925, ep11925, em11925, dsL]

theorem negative11925 :
    Eminus aL (agent11925.root+dsL) scalar11925.worldRadius world11925.frame
      agent11925.frame tm11925 ≤ -em11925 := by
  apply negative_check (lo := (4197170847937717651 / 6250000000000000000)) (hi := (67154733567003482417 / 100000000000000000000))
    (y := (-((3643805429194307223 / 5000000000000000000)))) (u := (48250640395824112203 / 100000000000000000000))
  · norm_num [world11925, agent11925, scalar11925, tp11925, tm11925, ep11925, em11925, dsL]
  · norm_num [world11925, agent11925, scalar11925, tp11925, tm11925, ep11925, em11925, dsL]
  · norm_num [world11925, agent11925, scalar11925, tp11925, tm11925, ep11925, em11925, dsL]
  · norm_num [world11925, agent11925, scalar11925, tp11925, tm11925, ep11925, em11925, dsL]
  · norm_num [world11925, agent11925, scalar11925, tp11925, tm11925, ep11925, em11925, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11925, agent11925, tp11925, tm11925, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11925, agent11925, tp11925, tm11925, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11925, agent11925, scalar11925, tp11925, tm11925, ep11925, em11925, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11925, agent11925, tp11925, tm11925, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11925, agent11925, scalar11925, tp11925, tm11925, ep11925, em11925, dsL]

theorem tails11925 :
    exp (-((11925:ℝ)*ep11925)) ≤ scalar11925.upperTail ∧
    exp (-((11925:ℝ)*em11925)) ≤ scalar11925.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11925:ℝ)) (by norm_num [ep11925]) ?_)
      (show bp11925^8 ≤ scalar11925.upperTail by norm_num [bp11925, scalar11925])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11925, bp11925, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11925:ℝ)) (by norm_num [em11925]) ?_)
      (show bm11925^8 ≤ scalar11925.lowerTail by norm_num [bm11925, scalar11925])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11925, bm11925, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11925 :
    agent11925.root+dsL+scalar11925.worldRadius < √(1/100/aL) ∧
    2*(agent11925.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11925, agent11925, scalar11925, tp11925, tm11925, ep11925, em11925, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11925, agent11925, scalar11925, tp11925, tm11925, ep11925, em11925, dsL]

noncomputable def master11925 : MasterCertificate 11925 world11925 agent11925 :=
  master scalar11925 dsL tp11925 tm11925 ep11925 em11925
    (by norm_num [dsL]) (by norm_num [tp11925]) (by norm_num [tm11925])
    (by norm_num [ep11925]) (by norm_num [em11925])
    positive11925 negative11925 tails11925.1 tails11925.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11925.1 tailGuards11925.2

theorem preserves11925 : master11925.toScalarCertificate = scalar11925 := rfl

noncomputable def tp11926 : ℝ := (604309397 / 2500000000)
noncomputable def tm11926 : ℝ := (-((6250251117 / 10000000000)))
noncomputable def ep11926 : ℝ := (28009868303633869 / 50000000000000000000)
noncomputable def em11926 : ℝ := (53952861371516093 / 100000000000000000000)
noncomputable def bp11926 : ℝ := (43382492561321612227 / 100000000000000000000)
noncomputable def bm11926 : ℝ := (44739997719612622689 / 100000000000000000000)

theorem positive11926 :
    Eplus aL (agent11926.root+dsL) scalar11926.worldRadius world11926.frame
      agent11926.frame tp11926 ≤ -ep11926 := by
  apply positive_check (eT := (58324022878491736497 / 50000000000000000000)) (y := (39744436380751858087 / 100000000000000000000)) (u := (148801700406332416823 / 100000000000000000000))
  · norm_num [world11926, agent11926, scalar11926, tp11926, tm11926, ep11926, em11926, dsL]
  · norm_num [world11926, agent11926, scalar11926, tp11926, tm11926, ep11926, em11926, dsL]
  · norm_num [world11926, agent11926, scalar11926, tp11926, tm11926, ep11926, em11926, dsL]
  · norm_num [world11926, agent11926, scalar11926, tp11926, tm11926, ep11926, em11926, dsL]
  · norm_num [world11926, agent11926, scalar11926, tp11926, tm11926, ep11926, em11926, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11926, agent11926, tp11926, tm11926, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11926, agent11926, scalar11926, tp11926, tm11926, ep11926, em11926, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11926, agent11926, tp11926, tm11926, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11926, agent11926, scalar11926, tp11926, tm11926, ep11926, em11926, dsL]

theorem negative11926 :
    Eminus aL (agent11926.root+dsL) scalar11926.worldRadius world11926.frame
      agent11926.frame tm11926 ≤ -em11926 := by
  apply negative_check (lo := (1678861788814275101 / 2500000000000000000)) (hi := (67154471552571004041 / 100000000000000000000))
    (y := (-((72875734987857459811 / 100000000000000000000)))) (u := (48250820658637173059 / 100000000000000000000))
  · norm_num [world11926, agent11926, scalar11926, tp11926, tm11926, ep11926, em11926, dsL]
  · norm_num [world11926, agent11926, scalar11926, tp11926, tm11926, ep11926, em11926, dsL]
  · norm_num [world11926, agent11926, scalar11926, tp11926, tm11926, ep11926, em11926, dsL]
  · norm_num [world11926, agent11926, scalar11926, tp11926, tm11926, ep11926, em11926, dsL]
  · norm_num [world11926, agent11926, scalar11926, tp11926, tm11926, ep11926, em11926, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11926, agent11926, tp11926, tm11926, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11926, agent11926, tp11926, tm11926, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11926, agent11926, scalar11926, tp11926, tm11926, ep11926, em11926, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11926, agent11926, tp11926, tm11926, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11926, agent11926, scalar11926, tp11926, tm11926, ep11926, em11926, dsL]

theorem tails11926 :
    exp (-((11926:ℝ)*ep11926)) ≤ scalar11926.upperTail ∧
    exp (-((11926:ℝ)*em11926)) ≤ scalar11926.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11926:ℝ)) (by norm_num [ep11926]) ?_)
      (show bp11926^8 ≤ scalar11926.upperTail by norm_num [bp11926, scalar11926])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11926, bp11926, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11926:ℝ)) (by norm_num [em11926]) ?_)
      (show bm11926^8 ≤ scalar11926.lowerTail by norm_num [bm11926, scalar11926])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11926, bm11926, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11926 :
    agent11926.root+dsL+scalar11926.worldRadius < √(1/100/aL) ∧
    2*(agent11926.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11926, agent11926, scalar11926, tp11926, tm11926, ep11926, em11926, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11926, agent11926, scalar11926, tp11926, tm11926, ep11926, em11926, dsL]

noncomputable def master11926 : MasterCertificate 11926 world11926 agent11926 :=
  master scalar11926 dsL tp11926 tm11926 ep11926 em11926
    (by norm_num [dsL]) (by norm_num [tp11926]) (by norm_num [tm11926])
    (by norm_num [ep11926]) (by norm_num [em11926])
    positive11926 negative11926 tails11926.1 tails11926.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11926.1 tailGuards11926.2

theorem preserves11926 : master11926.toScalarCertificate = scalar11926 := rfl

noncomputable def tp11927 : ℝ := (2417334611 / 10000000000)
noncomputable def tm11927 : ℝ := (-((6250466781 / 10000000000)))
noncomputable def ep11927 : ℝ := (56022595998626027 / 100000000000000000000)
noncomputable def em11927 : ℝ := (5395532981353799 / 10000000000000000000)
noncomputable def bp11927 : ℝ := (2711100349894348891 / 6250000000000000000)
noncomputable def bm11927 : ℝ := (22367667077594222609 / 50000000000000000000)

theorem positive11927 :
    Eplus aL (agent11927.root+dsL) scalar11927.worldRadius world11927.frame
      agent11927.frame tp11927 ≤ -ep11927 := by
  apply positive_check (eT := (29162080670019915223 / 25000000000000000000)) (y := (39745074627201824199 / 100000000000000000000)) (u := (148802650130933538001 / 100000000000000000000))
  · norm_num [world11927, agent11927, scalar11927, tp11927, tm11927, ep11927, em11927, dsL]
  · norm_num [world11927, agent11927, scalar11927, tp11927, tm11927, ep11927, em11927, dsL]
  · norm_num [world11927, agent11927, scalar11927, tp11927, tm11927, ep11927, em11927, dsL]
  · norm_num [world11927, agent11927, scalar11927, tp11927, tm11927, ep11927, em11927, dsL]
  · norm_num [world11927, agent11927, scalar11927, tp11927, tm11927, ep11927, em11927, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11927, agent11927, tp11927, tm11927, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11927, agent11927, scalar11927, tp11927, tm11927, ep11927, em11927, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11927, agent11927, tp11927, tm11927, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11927, agent11927, scalar11927, tp11927, tm11927, ep11927, em11927, dsL]

theorem negative11927 :
    Eminus aL (agent11927.root+dsL) scalar11927.worldRadius world11927.frame
      agent11927.frame tm11927 ≤ -em11927 := by
  apply negative_check (lo := (6715420994939328889 / 10000000000000000000)) (hi := (67154209949393288891 / 100000000000000000000))
    (y := (-((72875360793235731819 / 100000000000000000000)))) (u := (48251001210950825611 / 100000000000000000000))
  · norm_num [world11927, agent11927, scalar11927, tp11927, tm11927, ep11927, em11927, dsL]
  · norm_num [world11927, agent11927, scalar11927, tp11927, tm11927, ep11927, em11927, dsL]
  · norm_num [world11927, agent11927, scalar11927, tp11927, tm11927, ep11927, em11927, dsL]
  · norm_num [world11927, agent11927, scalar11927, tp11927, tm11927, ep11927, em11927, dsL]
  · norm_num [world11927, agent11927, scalar11927, tp11927, tm11927, ep11927, em11927, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11927, agent11927, tp11927, tm11927, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11927, agent11927, tp11927, tm11927, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11927, agent11927, scalar11927, tp11927, tm11927, ep11927, em11927, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11927, agent11927, tp11927, tm11927, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11927, agent11927, scalar11927, tp11927, tm11927, ep11927, em11927, dsL]

theorem tails11927 :
    exp (-((11927:ℝ)*ep11927)) ≤ scalar11927.upperTail ∧
    exp (-((11927:ℝ)*em11927)) ≤ scalar11927.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11927:ℝ)) (by norm_num [ep11927]) ?_)
      (show bp11927^8 ≤ scalar11927.upperTail by norm_num [bp11927, scalar11927])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11927, bp11927, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11927:ℝ)) (by norm_num [em11927]) ?_)
      (show bm11927^8 ≤ scalar11927.lowerTail by norm_num [bm11927, scalar11927])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11927, bm11927, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11927 :
    agent11927.root+dsL+scalar11927.worldRadius < √(1/100/aL) ∧
    2*(agent11927.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11927, agent11927, scalar11927, tp11927, tm11927, ep11927, em11927, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11927, agent11927, scalar11927, tp11927, tm11927, ep11927, em11927, dsL]

noncomputable def master11927 : MasterCertificate 11927 world11927 agent11927 :=
  master scalar11927 dsL tp11927 tm11927 ep11927 em11927
    (by norm_num [dsL]) (by norm_num [tp11927]) (by norm_num [tm11927])
    (by norm_num [ep11927]) (by norm_num [em11927])
    positive11927 negative11927 tails11927.1 tails11927.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11927.1 tailGuards11927.2

theorem preserves11927 : master11927.toScalarCertificate = scalar11927 := rfl

noncomputable def tp11928 : ℝ := (2417431581 / 10000000000)
noncomputable def tm11928 : ℝ := (-((6250682287 / 10000000000)))
noncomputable def ep11928 : ℝ := (11205090808387077 / 20000000000000000000)
noncomputable def em11928 : ℝ := (53957796990684049 / 100000000000000000000)
noncomputable def bp11928 : ℝ := (43372719747522616587 / 100000000000000000000)
noncomputable def bm11928 : ℝ := (44730671644431788349 / 100000000000000000000)

theorem positive11928 :
    Eplus aL (agent11928.root+dsL) scalar11928.worldRadius world11928.frame
      agent11928.frame tp11928 ≤ -ep11928 := by
  apply positive_check (eT := (58324299625627117747 / 50000000000000000000)) (y := (19872856307776004639 / 50000000000000000000)) (u := (74401799738767248579 / 50000000000000000000))
  · norm_num [world11928, agent11928, scalar11928, tp11928, tm11928, ep11928, em11928, dsL]
  · norm_num [world11928, agent11928, scalar11928, tp11928, tm11928, ep11928, em11928, dsL]
  · norm_num [world11928, agent11928, scalar11928, tp11928, tm11928, ep11928, em11928, dsL]
  · norm_num [world11928, agent11928, scalar11928, tp11928, tm11928, ep11928, em11928, dsL]
  · norm_num [world11928, agent11928, scalar11928, tp11928, tm11928, ep11928, em11928, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11928, agent11928, tp11928, tm11928, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11928, agent11928, scalar11928, tp11928, tm11928, ep11928, em11928, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11928, agent11928, tp11928, tm11928, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11928, agent11928, scalar11928, tp11928, tm11928, ep11928, em11928, dsL]

theorem negative11928 :
    Eminus aL (agent11928.root+dsL) scalar11928.worldRadius world11928.frame
      agent11928.frame tm11928 ≤ -em11928 := by
  apply negative_check (lo := (67153948954283516693 / 100000000000000000000)) (hi := (33576974477141758347 / 50000000000000000000))
    (y := (-((9109373317073461791 / 12500000000000000000)))) (u := (48251181793868523821 / 100000000000000000000))
  · norm_num [world11928, agent11928, scalar11928, tp11928, tm11928, ep11928, em11928, dsL]
  · norm_num [world11928, agent11928, scalar11928, tp11928, tm11928, ep11928, em11928, dsL]
  · norm_num [world11928, agent11928, scalar11928, tp11928, tm11928, ep11928, em11928, dsL]
  · norm_num [world11928, agent11928, scalar11928, tp11928, tm11928, ep11928, em11928, dsL]
  · norm_num [world11928, agent11928, scalar11928, tp11928, tm11928, ep11928, em11928, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11928, agent11928, tp11928, tm11928, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11928, agent11928, tp11928, tm11928, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11928, agent11928, scalar11928, tp11928, tm11928, ep11928, em11928, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11928, agent11928, tp11928, tm11928, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11928, agent11928, scalar11928, tp11928, tm11928, ep11928, em11928, dsL]

theorem tails11928 :
    exp (-((11928:ℝ)*ep11928)) ≤ scalar11928.upperTail ∧
    exp (-((11928:ℝ)*em11928)) ≤ scalar11928.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11928:ℝ)) (by norm_num [ep11928]) ?_)
      (show bp11928^8 ≤ scalar11928.upperTail by norm_num [bp11928, scalar11928])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11928, bp11928, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11928:ℝ)) (by norm_num [em11928]) ?_)
      (show bm11928^8 ≤ scalar11928.lowerTail by norm_num [bm11928, scalar11928])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11928, bm11928, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11928 :
    agent11928.root+dsL+scalar11928.worldRadius < √(1/100/aL) ∧
    2*(agent11928.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11928, agent11928, scalar11928, tp11928, tm11928, ep11928, em11928, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11928, agent11928, scalar11928, tp11928, tm11928, ep11928, em11928, dsL]

noncomputable def master11928 : MasterCertificate 11928 world11928 agent11928 :=
  master scalar11928 dsL tp11928 tm11928 ep11928 em11928
    (by norm_num [dsL]) (by norm_num [tp11928]) (by norm_num [tm11928])
    (by norm_num [ep11928]) (by norm_num [em11928])
    positive11928 negative11928 tails11928.1 tails11928.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11928.1 tailGuards11928.2

theorem preserves11928 : master11928.toScalarCertificate = scalar11928 := rfl

noncomputable def tp11929 : ℝ := (302191061 / 1250000000)
noncomputable def tm11929 : ℝ := (-((625089767 / 1000000000)))
noncomputable def ep11929 : ℝ := (56028309672047813 / 100000000000000000000)
noncomputable def em11929 : ℝ := (53960261988063969 / 100000000000000000000)
noncomputable def bp11929 : ℝ := (1355244865553935273 / 3125000000000000000)
noncomputable def bm11929 : ℝ := (22363005398742986417 / 50000000000000000000)

theorem positive11929 :
    Eplus aL (agent11929.root+dsL) scalar11929.worldRadius world11929.frame
      agent11929.frame tp11929 ≤ -ep11929 := by
  apply positive_check (eT := (116648875396265239107 / 100000000000000000000)) (y := (3974634994935226511 / 10000000000000000000)) (u := (29760909571238426091 / 20000000000000000000))
  · norm_num [world11929, agent11929, scalar11929, tp11929, tm11929, ep11929, em11929, dsL]
  · norm_num [world11929, agent11929, scalar11929, tp11929, tm11929, ep11929, em11929, dsL]
  · norm_num [world11929, agent11929, scalar11929, tp11929, tm11929, ep11929, em11929, dsL]
  · norm_num [world11929, agent11929, scalar11929, tp11929, tm11929, ep11929, em11929, dsL]
  · norm_num [world11929, agent11929, scalar11929, tp11929, tm11929, ep11929, em11929, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11929, agent11929, tp11929, tm11929, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11929, agent11929, scalar11929, tp11929, tm11929, ep11929, em11929, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11929, agent11929, tp11929, tm11929, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11929, agent11929, scalar11929, tp11929, tm11929, ep11929, em11929, dsL]

theorem negative11929 :
    Eminus aL (agent11929.root+dsL) scalar11929.worldRadius world11929.frame
      agent11929.frame tm11929 ≤ -em11929 := by
  apply negative_check (lo := (67153688417409958753 / 100000000000000000000)) (hi := (33576844208704979377 / 50000000000000000000))
    (y := (-((72874611699843396683 / 100000000000000000000)))) (u := (12062840664341604077 / 25000000000000000000))
  · norm_num [world11929, agent11929, scalar11929, tp11929, tm11929, ep11929, em11929, dsL]
  · norm_num [world11929, agent11929, scalar11929, tp11929, tm11929, ep11929, em11929, dsL]
  · norm_num [world11929, agent11929, scalar11929, tp11929, tm11929, ep11929, em11929, dsL]
  · norm_num [world11929, agent11929, scalar11929, tp11929, tm11929, ep11929, em11929, dsL]
  · norm_num [world11929, agent11929, scalar11929, tp11929, tm11929, ep11929, em11929, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11929, agent11929, tp11929, tm11929, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11929, agent11929, tp11929, tm11929, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11929, agent11929, scalar11929, tp11929, tm11929, ep11929, em11929, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11929, agent11929, tp11929, tm11929, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11929, agent11929, scalar11929, tp11929, tm11929, ep11929, em11929, dsL]

theorem tails11929 :
    exp (-((11929:ℝ)*ep11929)) ≤ scalar11929.upperTail ∧
    exp (-((11929:ℝ)*em11929)) ≤ scalar11929.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11929:ℝ)) (by norm_num [ep11929]) ?_)
      (show bp11929^8 ≤ scalar11929.upperTail by norm_num [bp11929, scalar11929])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11929, bp11929, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11929:ℝ)) (by norm_num [em11929]) ?_)
      (show bm11929^8 ≤ scalar11929.lowerTail by norm_num [bm11929, scalar11929])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11929, bm11929, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11929 :
    agent11929.root+dsL+scalar11929.worldRadius < √(1/100/aL) ∧
    2*(agent11929.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11929, agent11929, scalar11929, tp11929, tm11929, ep11929, em11929, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11929, agent11929, scalar11929, tp11929, tm11929, ep11929, em11929, dsL]

noncomputable def master11929 : MasterCertificate 11929 world11929 agent11929 :=
  master scalar11929 dsL tp11929 tm11929 ep11929 em11929
    (by norm_num [dsL]) (by norm_num [tp11929]) (by norm_num [tm11929])
    (by norm_num [ep11929]) (by norm_num [em11929])
    positive11929 negative11929 tails11929.1 tails11929.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11929.1 tailGuards11929.2

theorem preserves11929 : master11929.toScalarCertificate = scalar11929 := rfl

noncomputable def tp11930 : ℝ := (483525091 / 2000000000)
noncomputable def tm11930 : ℝ := (-((3125556547 / 5000000000)))
noncomputable def ep11930 : ℝ := (11206232999337533 / 20000000000000000000)
noncomputable def em11930 : ℝ := (10792545333591507 / 20000000000000000000)
noncomputable def bp11930 : ℝ := (8672590417173484299 / 20000000000000000000)
noncomputable def bm11930 : ℝ := (44721350372330018067 / 100000000000000000000)

theorem positive11930 :
    Eplus aL (agent11930.root+dsL) scalar11930.worldRadius world11930.frame
      agent11930.frame tp11930 ≤ -ep11930 := by
  apply positive_check (eT := (116649152029041918959 / 100000000000000000000)) (y := (19873494408777711897 / 50000000000000000000)) (u := (74402749262084996097 / 50000000000000000000))
  · norm_num [world11930, agent11930, scalar11930, tp11930, tm11930, ep11930, em11930, dsL]
  · norm_num [world11930, agent11930, scalar11930, tp11930, tm11930, ep11930, em11930, dsL]
  · norm_num [world11930, agent11930, scalar11930, tp11930, tm11930, ep11930, em11930, dsL]
  · norm_num [world11930, agent11930, scalar11930, tp11930, tm11930, ep11930, em11930, dsL]
  · norm_num [world11930, agent11930, scalar11930, tp11930, tm11930, ep11930, em11930, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11930, agent11930, tp11930, tm11930, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11930, agent11930, scalar11930, tp11930, tm11930, ep11930, em11930, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11930, agent11930, tp11930, tm11930, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11930, agent11930, scalar11930, tp11930, tm11930, ep11930, em11930, dsL]

theorem negative11930 :
    Eminus aL (agent11930.root+dsL) scalar11930.worldRadius world11930.frame
      agent11930.frame tm11930 ≤ -em11930 := by
  apply negative_check (lo := (3357671381863599099 / 5000000000000000000)) (hi := (67153427637271981981 / 100000000000000000000))
    (y := (-((2277319953939462981 / 3125000000000000000)))) (u := (301572141994603739 / 625000000000000000))
  · norm_num [world11930, agent11930, scalar11930, tp11930, tm11930, ep11930, em11930, dsL]
  · norm_num [world11930, agent11930, scalar11930, tp11930, tm11930, ep11930, em11930, dsL]
  · norm_num [world11930, agent11930, scalar11930, tp11930, tm11930, ep11930, em11930, dsL]
  · norm_num [world11930, agent11930, scalar11930, tp11930, tm11930, ep11930, em11930, dsL]
  · norm_num [world11930, agent11930, scalar11930, tp11930, tm11930, ep11930, em11930, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11930, agent11930, tp11930, tm11930, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11930, agent11930, tp11930, tm11930, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11930, agent11930, scalar11930, tp11930, tm11930, ep11930, em11930, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11930, agent11930, tp11930, tm11930, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11930, agent11930, scalar11930, tp11930, tm11930, ep11930, em11930, dsL]

theorem tails11930 :
    exp (-((11930:ℝ)*ep11930)) ≤ scalar11930.upperTail ∧
    exp (-((11930:ℝ)*em11930)) ≤ scalar11930.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11930:ℝ)) (by norm_num [ep11930]) ?_)
      (show bp11930^8 ≤ scalar11930.upperTail by norm_num [bp11930, scalar11930])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11930, bp11930, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11930:ℝ)) (by norm_num [em11930]) ?_)
      (show bm11930^8 ≤ scalar11930.lowerTail by norm_num [bm11930, scalar11930])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11930, bm11930, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11930 :
    agent11930.root+dsL+scalar11930.worldRadius < √(1/100/aL) ∧
    2*(agent11930.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11930, agent11930, scalar11930, tp11930, tm11930, ep11930, em11930, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11930, agent11930, scalar11930, tp11930, tm11930, ep11930, em11930, dsL]

noncomputable def master11930 : MasterCertificate 11930 world11930 agent11930 :=
  master scalar11930 dsL tp11930 tm11930 ep11930 em11930
    (by norm_num [dsL]) (by norm_num [tp11930]) (by norm_num [tm11930])
    (by norm_num [ep11930]) (by norm_num [em11930])
    positive11930 negative11930 tails11930.1 tails11930.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11930.1 tailGuards11930.2

theorem preserves11930 : master11930.toScalarCertificate = scalar11930 := rfl

noncomputable def tp11931 : ℝ := (120886111 / 500000000)
noncomputable def tm11931 : ℝ := (-((31256641 / 50000000)))
noncomputable def ep11931 : ℝ := (1120680359748277 / 2000000000000000000)
noncomputable def em11931 : ℝ := (13491297293946743 / 25000000000000000000)
noncomputable def bp11931 : ℝ := (43358070223626403797 / 100000000000000000000)
noncomputable def bm11931 : ℝ := (22358345802896239049 / 50000000000000000000)

theorem positive11931 :
    Eplus aL (agent11931.root+dsL) scalar11931.worldRadius world11931.frame
      agent11931.frame tp11931 ≤ -ep11931 := by
  apply positive_check (eT := (29162356800700665353 / 25000000000000000000)) (y := (7949524977613890161 / 20000000000000000000)) (u := (148806445035079590551 / 100000000000000000000))
  · norm_num [world11931, agent11931, scalar11931, tp11931, tm11931, ep11931, em11931, dsL]
  · norm_num [world11931, agent11931, scalar11931, tp11931, tm11931, ep11931, em11931, dsL]
  · norm_num [world11931, agent11931, scalar11931, tp11931, tm11931, ep11931, em11931, dsL]
  · norm_num [world11931, agent11931, scalar11931, tp11931, tm11931, ep11931, em11931, dsL]
  · norm_num [world11931, agent11931, scalar11931, tp11931, tm11931, ep11931, em11931, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11931, agent11931, tp11931, tm11931, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11931, agent11931, scalar11931, tp11931, tm11931, ep11931, em11931, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11931, agent11931, tp11931, tm11931, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11931, agent11931, scalar11931, tp11931, tm11931, ep11931, em11931, dsL]

theorem negative11931 :
    Eminus aL (agent11931.root+dsL) scalar11931.worldRadius world11931.frame
      agent11931.frame tm11931 ≤ -em11931 := by
  apply negative_check (lo := (13430633629906898903 / 20000000000000000000)) (hi := (16788292037383623629 / 25000000000000000000))
    (y := (-((72873863514607956787 / 100000000000000000000)))) (u := (48251723668288230807 / 100000000000000000000))
  · norm_num [world11931, agent11931, scalar11931, tp11931, tm11931, ep11931, em11931, dsL]
  · norm_num [world11931, agent11931, scalar11931, tp11931, tm11931, ep11931, em11931, dsL]
  · norm_num [world11931, agent11931, scalar11931, tp11931, tm11931, ep11931, em11931, dsL]
  · norm_num [world11931, agent11931, scalar11931, tp11931, tm11931, ep11931, em11931, dsL]
  · norm_num [world11931, agent11931, scalar11931, tp11931, tm11931, ep11931, em11931, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11931, agent11931, tp11931, tm11931, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11931, agent11931, tp11931, tm11931, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11931, agent11931, scalar11931, tp11931, tm11931, ep11931, em11931, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11931, agent11931, tp11931, tm11931, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11931, agent11931, scalar11931, tp11931, tm11931, ep11931, em11931, dsL]

theorem tails11931 :
    exp (-((11931:ℝ)*ep11931)) ≤ scalar11931.upperTail ∧
    exp (-((11931:ℝ)*em11931)) ≤ scalar11931.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11931:ℝ)) (by norm_num [ep11931]) ?_)
      (show bp11931^8 ≤ scalar11931.upperTail by norm_num [bp11931, scalar11931])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11931, bp11931, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11931:ℝ)) (by norm_num [em11931]) ?_)
      (show bm11931^8 ≤ scalar11931.lowerTail by norm_num [bm11931, scalar11931])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11931, bm11931, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11931 :
    agent11931.root+dsL+scalar11931.worldRadius < √(1/100/aL) ∧
    2*(agent11931.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11931, agent11931, scalar11931, tp11931, tm11931, ep11931, em11931, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11931, agent11931, scalar11931, tp11931, tm11931, ep11931, em11931, dsL]

noncomputable def master11931 : MasterCertificate 11931 world11931 agent11931 :=
  master scalar11931 dsL tp11931 tm11931 ep11931 em11931
    (by norm_num [dsL]) (by norm_num [tp11931]) (by norm_num [tm11931])
    (by norm_num [ep11931]) (by norm_num [em11931])
    positive11931 negative11931 tails11931.1 tails11931.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11931.1 tailGuards11931.2

theorem preserves11931 : master11931.toScalarCertificate = scalar11931 := rfl

noncomputable def tp11932 : ℝ := (483563807 / 2000000000)
noncomputable def tm11932 : ℝ := (-((3125771659 / 5000000000)))
noncomputable def ep11932 : ℝ := (56036868954532463 / 100000000000000000000)
noncomputable def em11932 : ℝ := (26983824916421653 / 50000000000000000000)
noncomputable def bp11932 : ℝ := (43353189910267295851 / 100000000000000000000)
noncomputable def bm11932 : ℝ := (2235601714177889919 / 5000000000000000000)

theorem positive11932 :
    Eplus aL (agent11932.root+dsL) scalar11932.worldRadius world11932.frame
      agent11932.frame tp11932 ≤ -ep11932 := by
  apply positive_check (eT := (1458121284875575529 / 1250000000000000000)) (y := (19874131154570086043 / 50000000000000000000)) (u := (148807393561737886609 / 100000000000000000000))
  · norm_num [world11932, agent11932, scalar11932, tp11932, tm11932, ep11932, em11932, dsL]
  · norm_num [world11932, agent11932, scalar11932, tp11932, tm11932, ep11932, em11932, dsL]
  · norm_num [world11932, agent11932, scalar11932, tp11932, tm11932, ep11932, em11932, dsL]
  · norm_num [world11932, agent11932, scalar11932, tp11932, tm11932, ep11932, em11932, dsL]
  · norm_num [world11932, agent11932, scalar11932, tp11932, tm11932, ep11932, em11932, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11932, agent11932, tp11932, tm11932, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11932, agent11932, scalar11932, tp11932, tm11932, ep11932, em11932, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11932, agent11932, tp11932, tm11932, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11932, agent11932, scalar11932, tp11932, tm11932, ep11932, em11932, dsL]

theorem negative11932 :
    Eminus aL (agent11932.root+dsL) scalar11932.worldRadius world11932.frame
      agent11932.frame tm11932 ≤ -em11932 := by
  apply negative_check (lo := (16788227135634620707 / 25000000000000000000)) (hi := (67152908542538482829 / 100000000000000000000))
    (y := (-((1821837230174609227 / 2500000000000000000)))) (u := (2412595213925322619 / 5000000000000000000))
  · norm_num [world11932, agent11932, scalar11932, tp11932, tm11932, ep11932, em11932, dsL]
  · norm_num [world11932, agent11932, scalar11932, tp11932, tm11932, ep11932, em11932, dsL]
  · norm_num [world11932, agent11932, scalar11932, tp11932, tm11932, ep11932, em11932, dsL]
  · norm_num [world11932, agent11932, scalar11932, tp11932, tm11932, ep11932, em11932, dsL]
  · norm_num [world11932, agent11932, scalar11932, tp11932, tm11932, ep11932, em11932, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11932, agent11932, tp11932, tm11932, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11932, agent11932, tp11932, tm11932, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11932, agent11932, scalar11932, tp11932, tm11932, ep11932, em11932, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11932, agent11932, tp11932, tm11932, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11932, agent11932, scalar11932, tp11932, tm11932, ep11932, em11932, dsL]

theorem tails11932 :
    exp (-((11932:ℝ)*ep11932)) ≤ scalar11932.upperTail ∧
    exp (-((11932:ℝ)*em11932)) ≤ scalar11932.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11932:ℝ)) (by norm_num [ep11932]) ?_)
      (show bp11932^8 ≤ scalar11932.upperTail by norm_num [bp11932, scalar11932])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11932, bp11932, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11932:ℝ)) (by norm_num [em11932]) ?_)
      (show bm11932^8 ≤ scalar11932.lowerTail by norm_num [bm11932, scalar11932])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11932, bm11932, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11932 :
    agent11932.root+dsL+scalar11932.worldRadius < √(1/100/aL) ∧
    2*(agent11932.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11932, agent11932, scalar11932, tp11932, tm11932, ep11932, em11932, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11932, agent11932, scalar11932, tp11932, tm11932, ep11932, em11932, dsL]

noncomputable def master11932 : MasterCertificate 11932 world11932 agent11932 :=
  master scalar11932 dsL tp11932 tm11932 ep11932 em11932
    (by norm_num [dsL]) (by norm_num [tp11932]) (by norm_num [tm11932])
    (by norm_num [ep11932]) (by norm_num [em11932])
    positive11932 negative11932 tails11932.1 tails11932.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11932.1 tailGuards11932.2

theorem preserves11932 : master11932.toScalarCertificate = scalar11932 := rfl

noncomputable def tp11933 : ℝ := (604478949 / 2500000000)
noncomputable def tm11933 : ℝ := (-((390734891 / 625000000)))
noncomputable def ep11933 : ℝ := (7004964903404613 / 12500000000000000000)
noncomputable def em11933 : ℝ := (26985054922167743 / 50000000000000000000)
noncomputable def bp11933 : ℝ := (10837077571567736463 / 25000000000000000000)
noncomputable def bm11933 : ℝ := (44707377601872683289 / 100000000000000000000)

theorem positive11933 :
    Eplus aL (agent11933.root+dsL) scalar11933.worldRadius world11933.frame
      agent11933.frame tp11933 ≤ -ep11933 := by
  apply positive_check (eT := (14581247252255276299 / 12500000000000000000)) (y := (4968612405036429021 / 12500000000000000000)) (u := (18601042670675160587 / 12500000000000000000))
  · norm_num [world11933, agent11933, scalar11933, tp11933, tm11933, ep11933, em11933, dsL]
  · norm_num [world11933, agent11933, scalar11933, tp11933, tm11933, ep11933, em11933, dsL]
  · norm_num [world11933, agent11933, scalar11933, tp11933, tm11933, ep11933, em11933, dsL]
  · norm_num [world11933, agent11933, scalar11933, tp11933, tm11933, ep11933, em11933, dsL]
  · norm_num [world11933, agent11933, scalar11933, tp11933, tm11933, ep11933, em11933, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11933, agent11933, tp11933, tm11933, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11933, agent11933, scalar11933, tp11933, tm11933, ep11933, em11933, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11933, agent11933, tp11933, tm11933, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11933, agent11933, scalar11933, tp11933, tm11933, ep11933, em11933, dsL]

theorem negative11933 :
    Eminus aL (agent11933.root+dsL) scalar11933.worldRadius world11933.frame
      agent11933.frame tm11933 ≤ -em11933 := by
  apply negative_check (lo := (67152649637508507733 / 100000000000000000000)) (hi := (33576324818754253867 / 50000000000000000000))
    (y := (-((9109139307427418923 / 12500000000000000000)))) (u := (12063021275420406441 / 25000000000000000000))
  · norm_num [world11933, agent11933, scalar11933, tp11933, tm11933, ep11933, em11933, dsL]
  · norm_num [world11933, agent11933, scalar11933, tp11933, tm11933, ep11933, em11933, dsL]
  · norm_num [world11933, agent11933, scalar11933, tp11933, tm11933, ep11933, em11933, dsL]
  · norm_num [world11933, agent11933, scalar11933, tp11933, tm11933, ep11933, em11933, dsL]
  · norm_num [world11933, agent11933, scalar11933, tp11933, tm11933, ep11933, em11933, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11933, agent11933, tp11933, tm11933, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11933, agent11933, tp11933, tm11933, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11933, agent11933, scalar11933, tp11933, tm11933, ep11933, em11933, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11933, agent11933, tp11933, tm11933, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11933, agent11933, scalar11933, tp11933, tm11933, ep11933, em11933, dsL]

theorem tails11933 :
    exp (-((11933:ℝ)*ep11933)) ≤ scalar11933.upperTail ∧
    exp (-((11933:ℝ)*em11933)) ≤ scalar11933.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11933:ℝ)) (by norm_num [ep11933]) ?_)
      (show bp11933^8 ≤ scalar11933.upperTail by norm_num [bp11933, scalar11933])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11933, bp11933, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11933:ℝ)) (by norm_num [em11933]) ?_)
      (show bm11933^8 ≤ scalar11933.lowerTail by norm_num [bm11933, scalar11933])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11933, bm11933, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11933 :
    agent11933.root+dsL+scalar11933.worldRadius < √(1/100/aL) ∧
    2*(agent11933.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11933, agent11933, scalar11933, tp11933, tm11933, ep11933, em11933, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11933, agent11933, scalar11933, tp11933, tm11933, ep11933, em11933, dsL]

noncomputable def master11933 : MasterCertificate 11933 world11933 agent11933 :=
  master scalar11933 dsL tp11933 tm11933 ep11933 em11933
    (by norm_num [dsL]) (by norm_num [tp11933]) (by norm_num [tm11933])
    (by norm_num [ep11933]) (by norm_num [em11933])
    positive11933 negative11933 tails11933.1 tails11933.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11933.1 tailGuards11933.2

theorem preserves11933 : master11933.toScalarCertificate = scalar11933 := rfl

end BstLean.Part281
