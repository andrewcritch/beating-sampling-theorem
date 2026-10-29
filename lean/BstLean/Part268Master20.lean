import BstLean.Part261Checker
import BstLean.Part268Scalar20
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12850 : ℝ := (58250139 / 250000000)
noncomputable def tm12850 : ℝ := (-((761600981 / 1250000000)))
noncomputable def ep12850 : ℝ := (25912842131482481 / 50000000000000000000)
noncomputable def em12850 : ℝ := (12614461388492847 / 25000000000000000000)
noncomputable def bp12850 : ℝ := (43498224993466986381 / 100000000000000000000)
noncomputable def bm12850 : ℝ := (5558062076410769529 / 12500000000000000000)

theorem positive12850 :
    Eplus aL (agent12850.root+dsL) scalar12850.worldRadius world12850.frame
      agent12850.frame tp12850 ≤ -ep12850 := by
  apply positive_check (eT := (4625514725259403801 / 4000000000000000000)) (y := (37965454938906368089 / 100000000000000000000)) (u := (146177952957108351209 / 100000000000000000000))
  · norm_num [world12850, agent12850, scalar12850, tp12850, tm12850, ep12850, em12850, dsL]
  · norm_num [world12850, agent12850, scalar12850, tp12850, tm12850, ep12850, em12850, dsL]
  · norm_num [world12850, agent12850, scalar12850, tp12850, tm12850, ep12850, em12850, dsL]
  · norm_num [world12850, agent12850, scalar12850, tp12850, tm12850, ep12850, em12850, dsL]
  · norm_num [world12850, agent12850, scalar12850, tp12850, tm12850, ep12850, em12850, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12850, agent12850, tp12850, tm12850, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12850, agent12850, scalar12850, tp12850, tm12850, ep12850, em12850, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12850, agent12850, tp12850, tm12850, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12850, agent12850, scalar12850, tp12850, tm12850, ep12850, em12850, dsL]

theorem negative12850 :
    Eminus aL (agent12850.root+dsL) scalar12850.worldRadius world12850.frame
      agent12850.frame tm12850 ≤ -em12850 := by
  apply negative_check (lo := (34195388928151734133 / 50000000000000000000)) (hi := (68390777856303468267 / 100000000000000000000))
    (y := (-((35832756261295696843 / 50000000000000000000)))) (u := (48838310727835700693 / 100000000000000000000))
  · norm_num [world12850, agent12850, scalar12850, tp12850, tm12850, ep12850, em12850, dsL]
  · norm_num [world12850, agent12850, scalar12850, tp12850, tm12850, ep12850, em12850, dsL]
  · norm_num [world12850, agent12850, scalar12850, tp12850, tm12850, ep12850, em12850, dsL]
  · norm_num [world12850, agent12850, scalar12850, tp12850, tm12850, ep12850, em12850, dsL]
  · norm_num [world12850, agent12850, scalar12850, tp12850, tm12850, ep12850, em12850, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12850, agent12850, tp12850, tm12850, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12850, agent12850, tp12850, tm12850, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12850, agent12850, scalar12850, tp12850, tm12850, ep12850, em12850, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12850, agent12850, tp12850, tm12850, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12850, agent12850, scalar12850, tp12850, tm12850, ep12850, em12850, dsL]

theorem tails12850 :
    exp (-((12850:ℝ)*ep12850)) ≤ scalar12850.upperTail ∧
    exp (-((12850:ℝ)*em12850)) ≤ scalar12850.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12850:ℝ)) (by norm_num [ep12850]) ?_)
      (show bp12850^8 ≤ scalar12850.upperTail by norm_num [bp12850, scalar12850])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12850, bp12850, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12850:ℝ)) (by norm_num [em12850]) ?_)
      (show bm12850^8 ≤ scalar12850.lowerTail by norm_num [bm12850, scalar12850])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12850, bm12850, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12850 :
    agent12850.root+dsL+scalar12850.worldRadius < √(1/100/aL) ∧
    2*(agent12850.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12850, agent12850, scalar12850, tp12850, tm12850, ep12850, em12850, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12850, agent12850, scalar12850, tp12850, tm12850, ep12850, em12850, dsL]

noncomputable def master12850 : MasterCertificate 12850 world12850 agent12850 :=
  master scalar12850 dsL tp12850 tm12850 ep12850 em12850
    (by norm_num [dsL]) (by norm_num [tp12850]) (by norm_num [tm12850])
    (by norm_num [ep12850]) (by norm_num [em12850])
    positive12850 negative12850 tails12850.1 tails12850.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12850.1 tailGuards12850.2

theorem preserves12850 : master12850.toScalarCertificate = scalar12850 := rfl

noncomputable def tp12851 : ℝ := (2330085819 / 10000000000)
noncomputable def tm12851 : ℝ := (-((6092979241 / 10000000000)))
noncomputable def ep12851 : ℝ := (6478516045337249 / 12500000000000000000)
noncomputable def em12851 : ℝ := (50459933049741541 / 100000000000000000000)
noncomputable def bp12851 : ℝ := (8698739904156391999 / 20000000000000000000)
noncomputable def bm12851 : ℝ := (44460201311968147123 / 100000000000000000000)

theorem positive12851 :
    Eplus aL (agent12851.root+dsL) scalar12851.worldRadius world12851.frame
      agent12851.frame tp12851 ≤ -ep12851 := by
  apply positive_check (eT := (115638082704923703711 / 100000000000000000000)) (y := (37966193171311541861 / 100000000000000000000)) (u := (73089516047054782437 / 50000000000000000000))
  · norm_num [world12851, agent12851, scalar12851, tp12851, tm12851, ep12851, em12851, dsL]
  · norm_num [world12851, agent12851, scalar12851, tp12851, tm12851, ep12851, em12851, dsL]
  · norm_num [world12851, agent12851, scalar12851, tp12851, tm12851, ep12851, em12851, dsL]
  · norm_num [world12851, agent12851, scalar12851, tp12851, tm12851, ep12851, em12851, dsL]
  · norm_num [world12851, agent12851, scalar12851, tp12851, tm12851, ep12851, em12851, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12851, agent12851, tp12851, tm12851, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12851, agent12851, scalar12851, tp12851, tm12851, ep12851, em12851, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12851, agent12851, tp12851, tm12851, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12851, agent12851, scalar12851, tp12851, tm12851, ep12851, em12851, dsL]

theorem negative12851 :
    Eminus aL (agent12851.root+dsL) scalar12851.worldRadius world12851.frame
      agent12851.frame tm12851 ≤ -em12851 := by
  apply negative_check (lo := (68390610109307147489 / 100000000000000000000)) (hi := (6839061010930714749 / 10000000000000000000))
    (y := (-((14333104558198465647 / 20000000000000000000)))) (u := (24419152856461201487 / 50000000000000000000))
  · norm_num [world12851, agent12851, scalar12851, tp12851, tm12851, ep12851, em12851, dsL]
  · norm_num [world12851, agent12851, scalar12851, tp12851, tm12851, ep12851, em12851, dsL]
  · norm_num [world12851, agent12851, scalar12851, tp12851, tm12851, ep12851, em12851, dsL]
  · norm_num [world12851, agent12851, scalar12851, tp12851, tm12851, ep12851, em12851, dsL]
  · norm_num [world12851, agent12851, scalar12851, tp12851, tm12851, ep12851, em12851, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12851, agent12851, tp12851, tm12851, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12851, agent12851, tp12851, tm12851, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12851, agent12851, scalar12851, tp12851, tm12851, ep12851, em12851, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12851, agent12851, tp12851, tm12851, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12851, agent12851, scalar12851, tp12851, tm12851, ep12851, em12851, dsL]

theorem tails12851 :
    exp (-((12851:ℝ)*ep12851)) ≤ scalar12851.upperTail ∧
    exp (-((12851:ℝ)*em12851)) ≤ scalar12851.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12851:ℝ)) (by norm_num [ep12851]) ?_)
      (show bp12851^8 ≤ scalar12851.upperTail by norm_num [bp12851, scalar12851])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12851, bp12851, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12851:ℝ)) (by norm_num [em12851]) ?_)
      (show bm12851^8 ≤ scalar12851.lowerTail by norm_num [bm12851, scalar12851])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12851, bm12851, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12851 :
    agent12851.root+dsL+scalar12851.worldRadius < √(1/100/aL) ∧
    2*(agent12851.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12851, agent12851, scalar12851, tp12851, tm12851, ep12851, em12851, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12851, agent12851, scalar12851, tp12851, tm12851, ep12851, em12851, dsL]

noncomputable def master12851 : MasterCertificate 12851 world12851 agent12851 :=
  master scalar12851 dsL tp12851 tm12851 ep12851 em12851
    (by norm_num [dsL]) (by norm_num [tp12851]) (by norm_num [tm12851])
    (by norm_num [ep12851]) (by norm_num [em12851])
    positive12851 negative12851 tails12851.1 tails12851.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12851.1 tailGuards12851.2

theorem preserves12851 : master12851.toScalarCertificate = scalar12851 := rfl

noncomputable def tp12852 : ℝ := (582541501 / 2500000000)
noncomputable def tm12852 : ℝ := (-((3046575191 / 5000000000)))
noncomputable def ep12852 : ℝ := (25915285579640523 / 50000000000000000000)
noncomputable def em12852 : ℝ := (50462019330150713 / 100000000000000000000)
noncomputable def bp12852 : ℝ := (8697835032727845237 / 20000000000000000000)
noncomputable def bm12852 : ℝ := (11113976765891648581 / 25000000000000000000)

theorem positive12852 :
    Eplus aL (agent12852.root+dsL) scalar12852.worldRadius world12852.frame
      agent12852.frame tp12852 ≤ -ep12852 := by
  apply positive_check (eT := (14454787097215689267 / 12500000000000000000)) (y := (9491732638503734289 / 25000000000000000000)) (u := (73090054998491173641 / 50000000000000000000))
  · norm_num [world12852, agent12852, scalar12852, tp12852, tm12852, ep12852, em12852, dsL]
  · norm_num [world12852, agent12852, scalar12852, tp12852, tm12852, ep12852, em12852, dsL]
  · norm_num [world12852, agent12852, scalar12852, tp12852, tm12852, ep12852, em12852, dsL]
  · norm_num [world12852, agent12852, scalar12852, tp12852, tm12852, ep12852, em12852, dsL]
  · norm_num [world12852, agent12852, scalar12852, tp12852, tm12852, ep12852, em12852, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12852, agent12852, tp12852, tm12852, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12852, agent12852, scalar12852, tp12852, tm12852, ep12852, em12852, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12852, agent12852, tp12852, tm12852, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12852, agent12852, scalar12852, tp12852, tm12852, ep12852, em12852, dsL]

theorem negative12852 :
    Eminus aL (agent12852.root+dsL) scalar12852.worldRadius world12852.frame
      agent12852.frame tm12852 ≤ -em12852 := by
  apply negative_check (lo := (68390443379918475437 / 100000000000000000000)) (hi := (34195221689959237719 / 50000000000000000000))
    (y := (-((35832765712754834959 / 50000000000000000000)))) (u := (1526196921749081527 / 3125000000000000000))
  · norm_num [world12852, agent12852, scalar12852, tp12852, tm12852, ep12852, em12852, dsL]
  · norm_num [world12852, agent12852, scalar12852, tp12852, tm12852, ep12852, em12852, dsL]
  · norm_num [world12852, agent12852, scalar12852, tp12852, tm12852, ep12852, em12852, dsL]
  · norm_num [world12852, agent12852, scalar12852, tp12852, tm12852, ep12852, em12852, dsL]
  · norm_num [world12852, agent12852, scalar12852, tp12852, tm12852, ep12852, em12852, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12852, agent12852, tp12852, tm12852, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12852, agent12852, tp12852, tm12852, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12852, agent12852, scalar12852, tp12852, tm12852, ep12852, em12852, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12852, agent12852, tp12852, tm12852, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12852, agent12852, scalar12852, tp12852, tm12852, ep12852, em12852, dsL]

theorem tails12852 :
    exp (-((12852:ℝ)*ep12852)) ≤ scalar12852.upperTail ∧
    exp (-((12852:ℝ)*em12852)) ≤ scalar12852.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12852:ℝ)) (by norm_num [ep12852]) ?_)
      (show bp12852^8 ≤ scalar12852.upperTail by norm_num [bp12852, scalar12852])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12852, bp12852, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12852:ℝ)) (by norm_num [em12852]) ?_)
      (show bm12852^8 ≤ scalar12852.lowerTail by norm_num [bm12852, scalar12852])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12852, bm12852, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12852 :
    agent12852.root+dsL+scalar12852.worldRadius < √(1/100/aL) ∧
    2*(agent12852.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12852, agent12852, scalar12852, tp12852, tm12852, ep12852, em12852, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12852, agent12852, scalar12852, tp12852, tm12852, ep12852, em12852, dsL]

noncomputable def master12852 : MasterCertificate 12852 world12852 agent12852 :=
  master scalar12852 dsL tp12852 tm12852 ep12852 em12852
    (by norm_num [dsL]) (by norm_num [tp12852]) (by norm_num [tm12852])
    (by norm_num [ep12852]) (by norm_num [em12852])
    positive12852 negative12852 tails12852.1 tails12852.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12852.1 tailGuards12852.2

theorem preserves12852 : master12852.toScalarCertificate = scalar12852 := rfl

noncomputable def tp12853 : ℝ := (1165123071 / 5000000000)
noncomputable def tm12853 : ℝ := (-((76166519 / 125000000)))
noncomputable def ep12853 : ℝ := (12958253200124483 / 25000000000000000000)
noncomputable def em12853 : ℝ := (50464104548630129 / 100000000000000000000)
noncomputable def bp12853 : ℝ := (21742325909377060871 / 50000000000000000000)
noncomputable def bm12853 : ℝ := (8890322751296726707 / 20000000000000000000)

theorem positive12853 :
    Eplus aL (agent12853.root+dsL) scalar12853.worldRadius world12853.frame
      agent12853.frame tp12853 ≤ -ep12853 := by
  apply positive_check (eT := (451712931814570001 / 390625000000000000)) (y := (3796766740745818681 / 10000000000000000000)) (u := (73090593567062331183 / 50000000000000000000))
  · norm_num [world12853, agent12853, scalar12853, tp12853, tm12853, ep12853, em12853, dsL]
  · norm_num [world12853, agent12853, scalar12853, tp12853, tm12853, ep12853, em12853, dsL]
  · norm_num [world12853, agent12853, scalar12853, tp12853, tm12853, ep12853, em12853, dsL]
  · norm_num [world12853, agent12853, scalar12853, tp12853, tm12853, ep12853, em12853, dsL]
  · norm_num [world12853, agent12853, scalar12853, tp12853, tm12853, ep12853, em12853, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12853, agent12853, tp12853, tm12853, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12853, agent12853, scalar12853, tp12853, tm12853, ep12853, em12853, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12853, agent12853, tp12853, tm12853, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12853, agent12853, scalar12853, tp12853, tm12853, ep12853, em12853, dsL]

theorem negative12853 :
    Eminus aL (agent12853.root+dsL) scalar12853.worldRadius world12853.frame
      agent12853.frame tm12853 ≤ -em12853 := by
  apply negative_check (lo := (68390276606349847237 / 100000000000000000000)) (hi := (34195138303174923619 / 50000000000000000000))
    (y := (-((71665540546369276993 / 100000000000000000000)))) (u := (305239356509361863 / 625000000000000000))
  · norm_num [world12853, agent12853, scalar12853, tp12853, tm12853, ep12853, em12853, dsL]
  · norm_num [world12853, agent12853, scalar12853, tp12853, tm12853, ep12853, em12853, dsL]
  · norm_num [world12853, agent12853, scalar12853, tp12853, tm12853, ep12853, em12853, dsL]
  · norm_num [world12853, agent12853, scalar12853, tp12853, tm12853, ep12853, em12853, dsL]
  · norm_num [world12853, agent12853, scalar12853, tp12853, tm12853, ep12853, em12853, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12853, agent12853, tp12853, tm12853, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12853, agent12853, tp12853, tm12853, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12853, agent12853, scalar12853, tp12853, tm12853, ep12853, em12853, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12853, agent12853, tp12853, tm12853, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12853, agent12853, scalar12853, tp12853, tm12853, ep12853, em12853, dsL]

theorem tails12853 :
    exp (-((12853:ℝ)*ep12853)) ≤ scalar12853.upperTail ∧
    exp (-((12853:ℝ)*em12853)) ≤ scalar12853.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12853:ℝ)) (by norm_num [ep12853]) ?_)
      (show bp12853^8 ≤ scalar12853.upperTail by norm_num [bp12853, scalar12853])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12853, bp12853, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12853:ℝ)) (by norm_num [em12853]) ?_)
      (show bm12853^8 ≤ scalar12853.lowerTail by norm_num [bm12853, scalar12853])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12853, bm12853, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12853 :
    agent12853.root+dsL+scalar12853.worldRadius < √(1/100/aL) ∧
    2*(agent12853.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12853, agent12853, scalar12853, tp12853, tm12853, ep12853, em12853, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12853, agent12853, scalar12853, tp12853, tm12853, ep12853, em12853, dsL]

noncomputable def master12853 : MasterCertificate 12853 world12853 agent12853 :=
  master scalar12853 dsL tp12853 tm12853 ep12853 em12853
    (by norm_num [dsL]) (by norm_num [tp12853]) (by norm_num [tm12853])
    (by norm_num [ep12853]) (by norm_num [em12853])
    positive12853 negative12853 tails12853.1 tails12853.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12853.1 tailGuards12853.2

theorem preserves12853 : master12853.toScalarCertificate = scalar12853 := rfl

noncomputable def tp12854 : ℝ := (1165163163 / 5000000000)
noncomputable def tm12854 : ℝ := (-((6093492661 / 10000000000)))
noncomputable def ep12854 : ℝ := (25917726811272783 / 50000000000000000000)
noncomputable def em12854 : ℝ := (50466188999254167 / 100000000000000000000)
noncomputable def bp12854 : ℝ := (43480129251224195877 / 100000000000000000000)
noncomputable def bm12854 : ℝ := (44447321180688275051 / 100000000000000000000)

theorem positive12854 :
    Eplus aL (agent12854.root+dsL) scalar12854.worldRadius world12854.frame
      agent12854.frame tp12854 ≤ -ep12854 := by
  apply positive_check (eT := (115638724675949476019 / 100000000000000000000)) (y := (7593681092500987869 / 20000000000000000000)) (u := (29236453207147029507 / 20000000000000000000))
  · norm_num [world12854, agent12854, scalar12854, tp12854, tm12854, ep12854, em12854, dsL]
  · norm_num [world12854, agent12854, scalar12854, tp12854, tm12854, ep12854, em12854, dsL]
  · norm_num [world12854, agent12854, scalar12854, tp12854, tm12854, ep12854, em12854, dsL]
  · norm_num [world12854, agent12854, scalar12854, tp12854, tm12854, ep12854, em12854, dsL]
  · norm_num [world12854, agent12854, scalar12854, tp12854, tm12854, ep12854, em12854, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12854, agent12854, tp12854, tm12854, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12854, agent12854, scalar12854, tp12854, tm12854, ep12854, em12854, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12854, agent12854, tp12854, tm12854, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12854, agent12854, scalar12854, tp12854, tm12854, ep12854, em12854, dsL]

theorem negative12854 :
    Eminus aL (agent12854.root+dsL) scalar12854.worldRadius world12854.frame
      agent12854.frame tm12854 ≤ -em12854 := by
  apply negative_check (lo := (34195054881482993891 / 50000000000000000000)) (hi := (68390109762965987783 / 100000000000000000000))
    (y := (-((71665550626336194569 / 100000000000000000000)))) (u := (24419146059306980651 / 50000000000000000000))
  · norm_num [world12854, agent12854, scalar12854, tp12854, tm12854, ep12854, em12854, dsL]
  · norm_num [world12854, agent12854, scalar12854, tp12854, tm12854, ep12854, em12854, dsL]
  · norm_num [world12854, agent12854, scalar12854, tp12854, tm12854, ep12854, em12854, dsL]
  · norm_num [world12854, agent12854, scalar12854, tp12854, tm12854, ep12854, em12854, dsL]
  · norm_num [world12854, agent12854, scalar12854, tp12854, tm12854, ep12854, em12854, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12854, agent12854, tp12854, tm12854, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12854, agent12854, tp12854, tm12854, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12854, agent12854, scalar12854, tp12854, tm12854, ep12854, em12854, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12854, agent12854, tp12854, tm12854, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12854, agent12854, scalar12854, tp12854, tm12854, ep12854, em12854, dsL]

theorem tails12854 :
    exp (-((12854:ℝ)*ep12854)) ≤ scalar12854.upperTail ∧
    exp (-((12854:ℝ)*em12854)) ≤ scalar12854.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12854:ℝ)) (by norm_num [ep12854]) ?_)
      (show bp12854^8 ≤ scalar12854.upperTail by norm_num [bp12854, scalar12854])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12854, bp12854, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12854:ℝ)) (by norm_num [em12854]) ?_)
      (show bm12854^8 ≤ scalar12854.lowerTail by norm_num [bm12854, scalar12854])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12854, bm12854, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12854 :
    agent12854.root+dsL+scalar12854.worldRadius < √(1/100/aL) ∧
    2*(agent12854.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12854, agent12854, scalar12854, tp12854, tm12854, ep12854, em12854, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12854, agent12854, scalar12854, tp12854, tm12854, ep12854, em12854, dsL]

noncomputable def master12854 : MasterCertificate 12854 world12854 agent12854 :=
  master scalar12854 dsL tp12854 tm12854 ep12854 em12854
    (by norm_num [dsL]) (by norm_num [tp12854]) (by norm_num [tm12854])
    (by norm_num [ep12854]) (by norm_num [em12854])
    positive12854 negative12854 tails12854.1 tails12854.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12854.1 tailGuards12854.2

theorem preserves12854 : master12854.toScalarCertificate = scalar12854 := rfl

noncomputable def tp12855 : ℝ := (2330406379 / 10000000000)
noncomputable def tm12855 : ℝ := (-((6093663641 / 10000000000)))
noncomputable def ep12855 : ℝ := (25918946172490901 / 50000000000000000000)
noncomputable def em12855 : ℝ := (3154266969586083 / 6250000000000000000)
noncomputable def bp12855 : ℝ := (8695121671110700503 / 20000000000000000000)
noncomputable def bm12855 : ℝ := (22221515085378902491 / 50000000000000000000)

theorem positive12855 :
    Eplus aL (agent12855.root+dsL) scalar12855.worldRadius world12855.frame
      agent12855.frame tp12855 ≤ -ep12855 := by
  apply positive_check (eT := (115638937895716142783 / 100000000000000000000)) (y := (9492285403959473871 / 25000000000000000000)) (u := (36545835541329934363 / 25000000000000000000))
  · norm_num [world12855, agent12855, scalar12855, tp12855, tm12855, ep12855, em12855, dsL]
  · norm_num [world12855, agent12855, scalar12855, tp12855, tm12855, ep12855, em12855, dsL]
  · norm_num [world12855, agent12855, scalar12855, tp12855, tm12855, ep12855, em12855, dsL]
  · norm_num [world12855, agent12855, scalar12855, tp12855, tm12855, ep12855, em12855, dsL]
  · norm_num [world12855, agent12855, scalar12855, tp12855, tm12855, ep12855, em12855, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12855, agent12855, tp12855, tm12855, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12855, agent12855, scalar12855, tp12855, tm12855, ep12855, em12855, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12855, agent12855, tp12855, tm12855, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12855, agent12855, scalar12855, tp12855, tm12855, ep12855, em12855, dsL]

theorem negative12855 :
    Eminus aL (agent12855.root+dsL) scalar12855.worldRadius world12855.frame
      agent12855.frame tm12855 ≤ -em12855 := by
  apply negative_check (lo := (17097485887291709103 / 25000000000000000000)) (hi := (68389943549166836413 / 100000000000000000000))
    (y := (-((71665559408554091449 / 100000000000000000000)))) (u := (48838287829528918669 / 100000000000000000000))
  · norm_num [world12855, agent12855, scalar12855, tp12855, tm12855, ep12855, em12855, dsL]
  · norm_num [world12855, agent12855, scalar12855, tp12855, tm12855, ep12855, em12855, dsL]
  · norm_num [world12855, agent12855, scalar12855, tp12855, tm12855, ep12855, em12855, dsL]
  · norm_num [world12855, agent12855, scalar12855, tp12855, tm12855, ep12855, em12855, dsL]
  · norm_num [world12855, agent12855, scalar12855, tp12855, tm12855, ep12855, em12855, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12855, agent12855, tp12855, tm12855, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12855, agent12855, tp12855, tm12855, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12855, agent12855, scalar12855, tp12855, tm12855, ep12855, em12855, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12855, agent12855, tp12855, tm12855, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12855, agent12855, scalar12855, tp12855, tm12855, ep12855, em12855, dsL]

theorem tails12855 :
    exp (-((12855:ℝ)*ep12855)) ≤ scalar12855.upperTail ∧
    exp (-((12855:ℝ)*em12855)) ≤ scalar12855.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12855:ℝ)) (by norm_num [ep12855]) ?_)
      (show bp12855^8 ≤ scalar12855.upperTail by norm_num [bp12855, scalar12855])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12855, bp12855, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12855:ℝ)) (by norm_num [em12855]) ?_)
      (show bm12855^8 ≤ scalar12855.lowerTail by norm_num [bm12855, scalar12855])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12855, bm12855, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12855 :
    agent12855.root+dsL+scalar12855.worldRadius < √(1/100/aL) ∧
    2*(agent12855.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12855, agent12855, scalar12855, tp12855, tm12855, ep12855, em12855, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12855, agent12855, scalar12855, tp12855, tm12855, ep12855, em12855, dsL]

noncomputable def master12855 : MasterCertificate 12855 world12855 agent12855 :=
  master scalar12855 dsL tp12855 tm12855 ep12855 em12855
    (by norm_num [dsL]) (by norm_num [tp12855]) (by norm_num [tm12855])
    (by norm_num [ep12855]) (by norm_num [em12855])
    positive12855 negative12855 tails12855.1 tails12855.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12855.1 tailGuards12855.2

theorem preserves12855 : master12855.toScalarCertificate = scalar12855 := rfl

noncomputable def tp12856 : ℝ := (2330486421 / 10000000000)
noncomputable def tm12856 : ℝ := (-((3046917207 / 5000000000)))
noncomputable def ep12856 : ℝ := (25920165359074371 / 50000000000000000000)
noncomputable def em12856 : ℝ := (6308794211894257 / 12500000000000000000)
noncomputable def bp12856 : ℝ := (43471087908905940377 / 100000000000000000000)
noncomputable def bm12856 : ℝ := (11109684895266435913 / 25000000000000000000)

theorem positive12856 :
    Eplus aL (agent12856.root+dsL) scalar12856.worldRadius world12856.frame
      agent12856.frame tp12856 ≤ -ep12856 := by
  apply positive_check (eT := (115639151069122698653 / 100000000000000000000)) (y := (18984938961767881003 / 50000000000000000000)) (u := (36546104632120941703 / 25000000000000000000))
  · norm_num [world12856, agent12856, scalar12856, tp12856, tm12856, ep12856, em12856, dsL]
  · norm_num [world12856, agent12856, scalar12856, tp12856, tm12856, ep12856, em12856, dsL]
  · norm_num [world12856, agent12856, scalar12856, tp12856, tm12856, ep12856, em12856, dsL]
  · norm_num [world12856, agent12856, scalar12856, tp12856, tm12856, ep12856, em12856, dsL]
  · norm_num [world12856, agent12856, scalar12856, tp12856, tm12856, ep12856, em12856, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12856, agent12856, tp12856, tm12856, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12856, agent12856, scalar12856, tp12856, tm12856, ep12856, em12856, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12856, agent12856, tp12856, tm12856, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12856, agent12856, scalar12856, tp12856, tm12856, ep12856, em12856, dsL]

theorem negative12856 :
    Eminus aL (agent12856.root+dsL) scalar12856.worldRadius world12856.frame
      agent12856.frame tm12856 ≤ -em12856 := by
  apply negative_check (lo := (68389778161000804417 / 100000000000000000000)) (hi := (34194889080500402209 / 50000000000000000000))
    (y := (-((8958195905887498619 / 12500000000000000000)))) (u := (9767656800263492327 / 20000000000000000000))
  · norm_num [world12856, agent12856, scalar12856, tp12856, tm12856, ep12856, em12856, dsL]
  · norm_num [world12856, agent12856, scalar12856, tp12856, tm12856, ep12856, em12856, dsL]
  · norm_num [world12856, agent12856, scalar12856, tp12856, tm12856, ep12856, em12856, dsL]
  · norm_num [world12856, agent12856, scalar12856, tp12856, tm12856, ep12856, em12856, dsL]
  · norm_num [world12856, agent12856, scalar12856, tp12856, tm12856, ep12856, em12856, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12856, agent12856, tp12856, tm12856, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12856, agent12856, tp12856, tm12856, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12856, agent12856, scalar12856, tp12856, tm12856, ep12856, em12856, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12856, agent12856, tp12856, tm12856, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12856, agent12856, scalar12856, tp12856, tm12856, ep12856, em12856, dsL]

theorem tails12856 :
    exp (-((12856:ℝ)*ep12856)) ≤ scalar12856.upperTail ∧
    exp (-((12856:ℝ)*em12856)) ≤ scalar12856.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12856:ℝ)) (by norm_num [ep12856]) ?_)
      (show bp12856^8 ≤ scalar12856.upperTail by norm_num [bp12856, scalar12856])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12856, bp12856, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12856:ℝ)) (by norm_num [em12856]) ?_)
      (show bm12856^8 ≤ scalar12856.lowerTail by norm_num [bm12856, scalar12856])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12856, bm12856, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12856 :
    agent12856.root+dsL+scalar12856.worldRadius < √(1/100/aL) ∧
    2*(agent12856.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12856, agent12856, scalar12856, tp12856, tm12856, ep12856, em12856, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12856, agent12856, scalar12856, tp12856, tm12856, ep12856, em12856, dsL]

noncomputable def master12856 : MasterCertificate 12856 world12856 agent12856 :=
  master scalar12856 dsL tp12856 tm12856 ep12856 em12856
    (by norm_num [dsL]) (by norm_num [tp12856]) (by norm_num [tm12856])
    (by norm_num [ep12856]) (by norm_num [em12856])
    positive12856 negative12856 tails12856.1 tails12856.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12856.1 tailGuards12856.2

theorem preserves12856 : master12856.toScalarCertificate = scalar12856 := rfl

noncomputable def tp12857 : ℝ := (291320801 / 1250000000)
noncomputable def tm12857 : ℝ := (-((6094005367 / 10000000000)))
noncomputable def ep12857 : ℝ := (25921383495830097 / 50000000000000000000)
noncomputable def em12857 : ℝ := (12618108485113659 / 25000000000000000000)
noncomputable def bp12857 : ℝ := (21733284567024781907 / 50000000000000000000)
noncomputable def bm12857 : ℝ := (22217225278581146109 / 50000000000000000000)

theorem positive12857 :
    Eplus aL (agent12857.root+dsL) scalar12857.worldRadius world12857.frame
      agent12857.frame tp12857 ≤ -ep12857 := by
  apply positive_check (eT := (57819681939458999681 / 50000000000000000000)) (y := (37970613659726605687 / 100000000000000000000)) (u := (29237098812822560569 / 20000000000000000000))
  · norm_num [world12857, agent12857, scalar12857, tp12857, tm12857, ep12857, em12857, dsL]
  · norm_num [world12857, agent12857, scalar12857, tp12857, tm12857, ep12857, em12857, dsL]
  · norm_num [world12857, agent12857, scalar12857, tp12857, tm12857, ep12857, em12857, dsL]
  · norm_num [world12857, agent12857, scalar12857, tp12857, tm12857, ep12857, em12857, dsL]
  · norm_num [world12857, agent12857, scalar12857, tp12857, tm12857, ep12857, em12857, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12857, agent12857, tp12857, tm12857, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12857, agent12857, scalar12857, tp12857, tm12857, ep12857, em12857, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12857, agent12857, tp12857, tm12857, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12857, agent12857, scalar12857, tp12857, tm12857, ep12857, em12857, dsL]

theorem negative12857 :
    Eminus aL (agent12857.root+dsL) scalar12857.worldRadius world12857.frame
      agent12857.frame tm12857 ≤ -em12857 := by
  apply negative_check (lo := (68389611948287072441 / 100000000000000000000)) (hi := (34194805974143536221 / 50000000000000000000))
    (y := (-((35832788542004045797 / 50000000000000000000)))) (u := (48838279197140581809 / 100000000000000000000))
  · norm_num [world12857, agent12857, scalar12857, tp12857, tm12857, ep12857, em12857, dsL]
  · norm_num [world12857, agent12857, scalar12857, tp12857, tm12857, ep12857, em12857, dsL]
  · norm_num [world12857, agent12857, scalar12857, tp12857, tm12857, ep12857, em12857, dsL]
  · norm_num [world12857, agent12857, scalar12857, tp12857, tm12857, ep12857, em12857, dsL]
  · norm_num [world12857, agent12857, scalar12857, tp12857, tm12857, ep12857, em12857, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12857, agent12857, tp12857, tm12857, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12857, agent12857, tp12857, tm12857, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12857, agent12857, scalar12857, tp12857, tm12857, ep12857, em12857, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12857, agent12857, tp12857, tm12857, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12857, agent12857, scalar12857, tp12857, tm12857, ep12857, em12857, dsL]

theorem tails12857 :
    exp (-((12857:ℝ)*ep12857)) ≤ scalar12857.upperTail ∧
    exp (-((12857:ℝ)*em12857)) ≤ scalar12857.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12857:ℝ)) (by norm_num [ep12857]) ?_)
      (show bp12857^8 ≤ scalar12857.upperTail by norm_num [bp12857, scalar12857])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12857, bp12857, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12857:ℝ)) (by norm_num [em12857]) ?_)
      (show bm12857^8 ≤ scalar12857.lowerTail by norm_num [bm12857, scalar12857])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12857, bm12857, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12857 :
    agent12857.root+dsL+scalar12857.worldRadius < √(1/100/aL) ∧
    2*(agent12857.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12857, agent12857, scalar12857, tp12857, tm12857, ep12857, em12857, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12857, agent12857, scalar12857, tp12857, tm12857, ep12857, em12857, dsL]

noncomputable def master12857 : MasterCertificate 12857 world12857 agent12857 :=
  master scalar12857 dsL tp12857 tm12857 ep12857 em12857
    (by norm_num [dsL]) (by norm_num [tp12857]) (by norm_num [tm12857])
    (by norm_num [ep12857]) (by norm_num [em12857])
    positive12857 negative12857 tails12857.1 tails12857.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12857.1 tailGuards12857.2

theorem preserves12857 : master12857.toScalarCertificate = scalar12857 := rfl

noncomputable def tp12858 : ℝ := (582661597 / 2500000000)
noncomputable def tm12858 : ℝ := (-((6094176019 / 10000000000)))
noncomputable def ep12858 : ℝ := (12961300612720237 / 25000000000000000000)
noncomputable def em12858 : ℝ := (50474513422213391 / 100000000000000000000)
noncomputable def bp12858 : ℝ := (43462051133019305059 / 100000000000000000000)
noncomputable def bm12858 : ℝ := (44430162261399826001 / 100000000000000000000)

theorem positive12858 :
    Eplus aL (agent12858.root+dsL) scalar12858.worldRadius world12858.frame
      agent12858.frame tp12858 ≤ -ep12858 := by
  apply positive_check (eT := (7227473541948280163 / 6250000000000000000)) (y := (37971349669161954751 / 100000000000000000000)) (u := (146186570007101742463 / 100000000000000000000))
  · norm_num [world12858, agent12858, scalar12858, tp12858, tm12858, ep12858, em12858, dsL]
  · norm_num [world12858, agent12858, scalar12858, tp12858, tm12858, ep12858, em12858, dsL]
  · norm_num [world12858, agent12858, scalar12858, tp12858, tm12858, ep12858, em12858, dsL]
  · norm_num [world12858, agent12858, scalar12858, tp12858, tm12858, ep12858, em12858, dsL]
  · norm_num [world12858, agent12858, scalar12858, tp12858, tm12858, ep12858, em12858, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12858, agent12858, tp12858, tm12858, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12858, agent12858, scalar12858, tp12858, tm12858, ep12858, em12858, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12858, agent12858, tp12858, tm12858, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12858, agent12858, scalar12858, tp12858, tm12858, ep12858, em12858, dsL]

theorem negative12858 :
    Eminus aL (agent12858.root+dsL) scalar12858.worldRadius world12858.frame
      agent12858.frame tm12858 ≤ -em12858 := by
  apply negative_check (lo := (68389446962029999077 / 100000000000000000000)) (hi := (34194723481014999539 / 50000000000000000000))
    (y := (-((71665584940112341363 / 100000000000000000000)))) (u := (48838275360354604999 / 100000000000000000000))
  · norm_num [world12858, agent12858, scalar12858, tp12858, tm12858, ep12858, em12858, dsL]
  · norm_num [world12858, agent12858, scalar12858, tp12858, tm12858, ep12858, em12858, dsL]
  · norm_num [world12858, agent12858, scalar12858, tp12858, tm12858, ep12858, em12858, dsL]
  · norm_num [world12858, agent12858, scalar12858, tp12858, tm12858, ep12858, em12858, dsL]
  · norm_num [world12858, agent12858, scalar12858, tp12858, tm12858, ep12858, em12858, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12858, agent12858, tp12858, tm12858, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12858, agent12858, tp12858, tm12858, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12858, agent12858, scalar12858, tp12858, tm12858, ep12858, em12858, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12858, agent12858, tp12858, tm12858, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12858, agent12858, scalar12858, tp12858, tm12858, ep12858, em12858, dsL]

theorem tails12858 :
    exp (-((12858:ℝ)*ep12858)) ≤ scalar12858.upperTail ∧
    exp (-((12858:ℝ)*em12858)) ≤ scalar12858.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12858:ℝ)) (by norm_num [ep12858]) ?_)
      (show bp12858^8 ≤ scalar12858.upperTail by norm_num [bp12858, scalar12858])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12858, bp12858, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12858:ℝ)) (by norm_num [em12858]) ?_)
      (show bm12858^8 ≤ scalar12858.lowerTail by norm_num [bm12858, scalar12858])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12858, bm12858, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12858 :
    agent12858.root+dsL+scalar12858.worldRadius < √(1/100/aL) ∧
    2*(agent12858.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12858, agent12858, scalar12858, tp12858, tm12858, ep12858, em12858, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12858, agent12858, scalar12858, tp12858, tm12858, ep12858, em12858, dsL]

noncomputable def master12858 : MasterCertificate 12858 world12858 agent12858 :=
  master scalar12858 dsL tp12858 tm12858 ep12858 em12858
    (by norm_num [dsL]) (by norm_num [tp12858]) (by norm_num [tm12858])
    (by norm_num [ep12858]) (by norm_num [em12858])
    positive12858 negative12858 tails12858.1 tails12858.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12858.1 tailGuards12858.2

theorem preserves12858 : master12858.toScalarCertificate = scalar12858 := rfl

noncomputable def tp12859 : ℝ := (1165363177 / 5000000000)
noncomputable def tm12859 : ℝ := (-((6094346589 / 10000000000)))
noncomputable def ep12859 : ℝ := (6480954594362763 / 12500000000000000000)
noncomputable def em12859 : ℝ := (50476591842409967 / 100000000000000000000)
noncomputable def bp12859 : ℝ := (21728767071968891783 / 50000000000000000000)
noncomputable def bm12859 : ℝ := (1777034996263524269 / 4000000000000000000)

theorem positive12859 :
    Eplus aL (agent12859.root+dsL) scalar12859.worldRadius world12859.frame
      agent12859.frame tp12859 ≤ -ep12859 := by
  apply positive_check (eT := (115639789395428041719 / 100000000000000000000)) (y := (18986042863099732423 / 50000000000000000000)) (u := (73093823013799115897 / 50000000000000000000))
  · norm_num [world12859, agent12859, scalar12859, tp12859, tm12859, ep12859, em12859, dsL]
  · norm_num [world12859, agent12859, scalar12859, tp12859, tm12859, ep12859, em12859, dsL]
  · norm_num [world12859, agent12859, scalar12859, tp12859, tm12859, ep12859, em12859, dsL]
  · norm_num [world12859, agent12859, scalar12859, tp12859, tm12859, ep12859, em12859, dsL]
  · norm_num [world12859, agent12859, scalar12859, tp12859, tm12859, ep12859, em12859, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12859, agent12859, tp12859, tm12859, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12859, agent12859, scalar12859, tp12859, tm12859, ep12859, em12859, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12859, agent12859, tp12859, tm12859, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12859, agent12859, scalar12859, tp12859, tm12859, ep12859, em12859, dsL]

theorem negative12859 :
    Eminus aL (agent12859.root+dsL) scalar12859.worldRadius world12859.frame
      agent12859.frame tm12859 ≤ -em12859 := by
  apply negative_check (lo := (34194641134184025027 / 50000000000000000000)) (hi := (13677856453673610011 / 20000000000000000000))
    (y := (-((71665592517175665261 / 100000000000000000000)))) (u := (1220956791496192371 / 2500000000000000000))
  · norm_num [world12859, agent12859, scalar12859, tp12859, tm12859, ep12859, em12859, dsL]
  · norm_num [world12859, agent12859, scalar12859, tp12859, tm12859, ep12859, em12859, dsL]
  · norm_num [world12859, agent12859, scalar12859, tp12859, tm12859, ep12859, em12859, dsL]
  · norm_num [world12859, agent12859, scalar12859, tp12859, tm12859, ep12859, em12859, dsL]
  · norm_num [world12859, agent12859, scalar12859, tp12859, tm12859, ep12859, em12859, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12859, agent12859, tp12859, tm12859, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12859, agent12859, tp12859, tm12859, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12859, agent12859, scalar12859, tp12859, tm12859, ep12859, em12859, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12859, agent12859, tp12859, tm12859, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12859, agent12859, scalar12859, tp12859, tm12859, ep12859, em12859, dsL]

theorem tails12859 :
    exp (-((12859:ℝ)*ep12859)) ≤ scalar12859.upperTail ∧
    exp (-((12859:ℝ)*em12859)) ≤ scalar12859.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12859:ℝ)) (by norm_num [ep12859]) ?_)
      (show bp12859^8 ≤ scalar12859.upperTail by norm_num [bp12859, scalar12859])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12859, bp12859, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12859:ℝ)) (by norm_num [em12859]) ?_)
      (show bm12859^8 ≤ scalar12859.lowerTail by norm_num [bm12859, scalar12859])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12859, bm12859, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12859 :
    agent12859.root+dsL+scalar12859.worldRadius < √(1/100/aL) ∧
    2*(agent12859.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12859, agent12859, scalar12859, tp12859, tm12859, ep12859, em12859, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12859, agent12859, scalar12859, tp12859, tm12859, ep12859, em12859, dsL]

noncomputable def master12859 : MasterCertificate 12859 world12859 agent12859 :=
  master scalar12859 dsL tp12859 tm12859 ep12859 em12859
    (by norm_num [dsL]) (by norm_num [tp12859]) (by norm_num [tm12859])
    (by norm_num [ep12859]) (by norm_num [em12859])
    positive12859 negative12859 tails12859.1 tails12859.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12859.1 tailGuards12859.2

theorem preserves12859 : master12859.toScalarCertificate = scalar12859 := rfl

noncomputable def tp12860 : ℝ := (116543963 / 500000000)
noncomputable def tm12860 : ℝ := (-((30473691 / 50000000)))
noncomputable def ep12860 : ℝ := (2074058349879567 / 4000000000000000000)
noncomputable def em12860 : ℝ := (50480183614861123 / 100000000000000000000)
noncomputable def bp12860 : ℝ := (8690409612098154487 / 20000000000000000000)
noncomputable def bm12860 : ℝ := (8884101419549255733 / 20000000000000000000)

theorem positive12860 :
    Eplus aL (agent12860.root+dsL) scalar12860.worldRadius world12860.frame
      agent12860.frame tp12860 ≤ -ep12860 := by
  apply positive_check (eT := (57820264005844505647 / 50000000000000000000)) (y := (7594420039407714329 / 20000000000000000000)) (u := (146187667182178813087 / 100000000000000000000))
  · norm_num [world12860, agent12860, scalar12860, tp12860, tm12860, ep12860, em12860, dsL]
  · norm_num [world12860, agent12860, scalar12860, tp12860, tm12860, ep12860, em12860, dsL]
  · norm_num [world12860, agent12860, scalar12860, tp12860, tm12860, ep12860, em12860, dsL]
  · norm_num [world12860, agent12860, scalar12860, tp12860, tm12860, ep12860, em12860, dsL]
  · norm_num [world12860, agent12860, scalar12860, tp12860, tm12860, ep12860, em12860, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12860, agent12860, tp12860, tm12860, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12860, agent12860, scalar12860, tp12860, tm12860, ep12860, em12860, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12860, agent12860, tp12860, tm12860, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12860, agent12860, scalar12860, tp12860, tm12860, ep12860, em12860, dsL]

theorem negative12860 :
    Eminus aL (agent12860.root+dsL) scalar12860.worldRadius world12860.frame
      agent12860.frame tm12860 ≤ -em12860 := by
  apply negative_check (lo := (34194087541364287673 / 50000000000000000000)) (hi := (68388175082728575347 / 100000000000000000000))
    (y := (-((1433274250207993363 / 2000000000000000000)))) (u := (48839189831294995523 / 100000000000000000000))
  · norm_num [world12860, agent12860, scalar12860, tp12860, tm12860, ep12860, em12860, dsL]
  · norm_num [world12860, agent12860, scalar12860, tp12860, tm12860, ep12860, em12860, dsL]
  · norm_num [world12860, agent12860, scalar12860, tp12860, tm12860, ep12860, em12860, dsL]
  · norm_num [world12860, agent12860, scalar12860, tp12860, tm12860, ep12860, em12860, dsL]
  · norm_num [world12860, agent12860, scalar12860, tp12860, tm12860, ep12860, em12860, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12860, agent12860, tp12860, tm12860, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12860, agent12860, tp12860, tm12860, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12860, agent12860, scalar12860, tp12860, tm12860, ep12860, em12860, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12860, agent12860, tp12860, tm12860, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12860, agent12860, scalar12860, tp12860, tm12860, ep12860, em12860, dsL]

theorem tails12860 :
    exp (-((12860:ℝ)*ep12860)) ≤ scalar12860.upperTail ∧
    exp (-((12860:ℝ)*em12860)) ≤ scalar12860.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12860:ℝ)) (by norm_num [ep12860]) ?_)
      (show bp12860^8 ≤ scalar12860.upperTail by norm_num [bp12860, scalar12860])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12860, bp12860, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12860:ℝ)) (by norm_num [em12860]) ?_)
      (show bm12860^8 ≤ scalar12860.lowerTail by norm_num [bm12860, scalar12860])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12860, bm12860, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12860 :
    agent12860.root+dsL+scalar12860.worldRadius < √(1/100/aL) ∧
    2*(agent12860.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12860, agent12860, scalar12860, tp12860, tm12860, ep12860, em12860, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12860, agent12860, scalar12860, tp12860, tm12860, ep12860, em12860, dsL]

noncomputable def master12860 : MasterCertificate 12860 world12860 agent12860 :=
  master scalar12860 dsL tp12860 tm12860 ep12860 em12860
    (by norm_num [dsL]) (by norm_num [tp12860]) (by norm_num [tm12860])
    (by norm_num [ep12860]) (by norm_num [em12860])
    positive12860 negative12860 tails12860.1 tails12860.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12860.1 tailGuards12860.2

theorem preserves12860 : master12860.toScalarCertificate = scalar12860 := rfl

noncomputable def tp12861 : ℝ := (1165479543 / 5000000000)
noncomputable def tm12861 : ℝ := (-((6094908579 / 10000000000)))
noncomputable def ep12861 : ℝ := (6481736315941033 / 12500000000000000000)
noncomputable def em12861 : ℝ := (50482259677982131 / 100000000000000000000)
noncomputable def bp12861 : ℝ := (5430941658677698347 / 12500000000000000000)
noncomputable def bm12861 : ℝ := (44416221812085426039 / 100000000000000000000)

theorem positive12861 :
    Eplus aL (agent12861.root+dsL) scalar12861.worldRadius world12861.frame
      agent12861.frame tp12861 ≤ -ep12861 := by
  apply positive_check (eT := (23128147956412974231 / 20000000000000000000)) (y := (37972834515171865617 / 100000000000000000000)) (u := (146188740668668969421 / 100000000000000000000))
  · norm_num [world12861, agent12861, scalar12861, tp12861, tm12861, ep12861, em12861, dsL]
  · norm_num [world12861, agent12861, scalar12861, tp12861, tm12861, ep12861, em12861, dsL]
  · norm_num [world12861, agent12861, scalar12861, tp12861, tm12861, ep12861, em12861, dsL]
  · norm_num [world12861, agent12861, scalar12861, tp12861, tm12861, ep12861, em12861, dsL]
  · norm_num [world12861, agent12861, scalar12861, tp12861, tm12861, ep12861, em12861, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12861, agent12861, tp12861, tm12861, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12861, agent12861, scalar12861, tp12861, tm12861, ep12861, em12861, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12861, agent12861, tp12861, tm12861, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12861, agent12861, scalar12861, tp12861, tm12861, ep12861, em12861, dsL]

theorem negative12861 :
    Eminus aL (agent12861.root+dsL) scalar12861.worldRadius world12861.frame
      agent12861.frame tm12861 ≤ -em12861 := by
  apply negative_check (lo := (17097002778006430311 / 25000000000000000000)) (hi := (13677602222405144249 / 20000000000000000000))
    (y := (-((14332743866401787681 / 20000000000000000000)))) (u := (48839186499676408109 / 100000000000000000000))
  · norm_num [world12861, agent12861, scalar12861, tp12861, tm12861, ep12861, em12861, dsL]
  · norm_num [world12861, agent12861, scalar12861, tp12861, tm12861, ep12861, em12861, dsL]
  · norm_num [world12861, agent12861, scalar12861, tp12861, tm12861, ep12861, em12861, dsL]
  · norm_num [world12861, agent12861, scalar12861, tp12861, tm12861, ep12861, em12861, dsL]
  · norm_num [world12861, agent12861, scalar12861, tp12861, tm12861, ep12861, em12861, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12861, agent12861, tp12861, tm12861, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12861, agent12861, tp12861, tm12861, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12861, agent12861, scalar12861, tp12861, tm12861, ep12861, em12861, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12861, agent12861, tp12861, tm12861, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12861, agent12861, scalar12861, tp12861, tm12861, ep12861, em12861, dsL]

theorem tails12861 :
    exp (-((12861:ℝ)*ep12861)) ≤ scalar12861.upperTail ∧
    exp (-((12861:ℝ)*em12861)) ≤ scalar12861.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12861:ℝ)) (by norm_num [ep12861]) ?_)
      (show bp12861^8 ≤ scalar12861.upperTail by norm_num [bp12861, scalar12861])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12861, bp12861, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12861:ℝ)) (by norm_num [em12861]) ?_)
      (show bm12861^8 ≤ scalar12861.lowerTail by norm_num [bm12861, scalar12861])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12861, bm12861, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12861 :
    agent12861.root+dsL+scalar12861.worldRadius < √(1/100/aL) ∧
    2*(agent12861.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12861, agent12861, scalar12861, tp12861, tm12861, ep12861, em12861, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12861, agent12861, scalar12861, tp12861, tm12861, ep12861, em12861, dsL]

noncomputable def master12861 : MasterCertificate 12861 world12861 agent12861 :=
  master scalar12861 dsL tp12861 tm12861 ep12861 em12861
    (by norm_num [dsL]) (by norm_num [tp12861]) (by norm_num [tm12861])
    (by norm_num [ep12861]) (by norm_num [em12861])
    positive12861 negative12861 tails12861.1 tails12861.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12861.1 tailGuards12861.2

theorem preserves12861 : master12861.toScalarCertificate = scalar12861 := rfl

noncomputable def tp12862 : ℝ := (1165519459 / 5000000000)
noncomputable def tm12862 : ℝ := (-((6095078909 / 10000000000)))
noncomputable def ep12862 : ℝ := (5185632071443527 / 10000000000000000000)
noncomputable def em12862 : ℝ := (3155270892412193 / 6250000000000000000)
noncomputable def bp12862 : ℝ := (43443019796422805169 / 100000000000000000000)
noncomputable def bm12862 : ℝ := (44411937753603811359 / 100000000000000000000)

theorem positive12862 :
    Eplus aL (agent12862.root+dsL) scalar12862.worldRadius world12862.frame
      agent12862.frame tp12862 ≤ -ep12862 := by
  apply positive_check (eT := (115640951628641727979 / 100000000000000000000)) (y := (9493392345439068893 / 25000000000000000000)) (u := (146189814964821630083 / 100000000000000000000))
  · norm_num [world12862, agent12862, scalar12862, tp12862, tm12862, ep12862, em12862, dsL]
  · norm_num [world12862, agent12862, scalar12862, tp12862, tm12862, ep12862, em12862, dsL]
  · norm_num [world12862, agent12862, scalar12862, tp12862, tm12862, ep12862, em12862, dsL]
  · norm_num [world12862, agent12862, scalar12862, tp12862, tm12862, ep12862, em12862, dsL]
  · norm_num [world12862, agent12862, scalar12862, tp12862, tm12862, ep12862, em12862, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12862, agent12862, tp12862, tm12862, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12862, agent12862, scalar12862, tp12862, tm12862, ep12862, em12862, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12862, agent12862, tp12862, tm12862, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12862, agent12862, scalar12862, tp12862, tm12862, ep12862, em12862, dsL]

theorem negative12862 :
    Eminus aL (agent12862.root+dsL) scalar12862.worldRadius world12862.frame
      agent12862.frame tm12862 ≤ -em12862 := by
  apply negative_check (lo := (17096961823299972807 / 25000000000000000000)) (hi := (68387847293199891229 / 100000000000000000000))
    (y := (-((71663726476759533299 / 100000000000000000000)))) (u := (48839183010238464787 / 100000000000000000000))
  · norm_num [world12862, agent12862, scalar12862, tp12862, tm12862, ep12862, em12862, dsL]
  · norm_num [world12862, agent12862, scalar12862, tp12862, tm12862, ep12862, em12862, dsL]
  · norm_num [world12862, agent12862, scalar12862, tp12862, tm12862, ep12862, em12862, dsL]
  · norm_num [world12862, agent12862, scalar12862, tp12862, tm12862, ep12862, em12862, dsL]
  · norm_num [world12862, agent12862, scalar12862, tp12862, tm12862, ep12862, em12862, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12862, agent12862, tp12862, tm12862, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12862, agent12862, tp12862, tm12862, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12862, agent12862, scalar12862, tp12862, tm12862, ep12862, em12862, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12862, agent12862, tp12862, tm12862, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12862, agent12862, scalar12862, tp12862, tm12862, ep12862, em12862, dsL]

theorem tails12862 :
    exp (-((12862:ℝ)*ep12862)) ≤ scalar12862.upperTail ∧
    exp (-((12862:ℝ)*em12862)) ≤ scalar12862.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12862:ℝ)) (by norm_num [ep12862]) ?_)
      (show bp12862^8 ≤ scalar12862.upperTail by norm_num [bp12862, scalar12862])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12862, bp12862, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12862:ℝ)) (by norm_num [em12862]) ?_)
      (show bm12862^8 ≤ scalar12862.lowerTail by norm_num [bm12862, scalar12862])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12862, bm12862, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12862 :
    agent12862.root+dsL+scalar12862.worldRadius < √(1/100/aL) ∧
    2*(agent12862.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12862, agent12862, scalar12862, tp12862, tm12862, ep12862, em12862, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12862, agent12862, scalar12862, tp12862, tm12862, ep12862, em12862, dsL]

noncomputable def master12862 : MasterCertificate 12862 world12862 agent12862 :=
  master scalar12862 dsL tp12862 tm12862 ep12862 em12862
    (by norm_num [dsL]) (by norm_num [tp12862]) (by norm_num [tm12862])
    (by norm_num [ep12862]) (by norm_num [em12862])
    positive12862 negative12862 tails12862.1 tails12862.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12862.1 tailGuards12862.2

theorem preserves12862 : master12862.toScalarCertificate = scalar12862 := rfl

noncomputable def tp12863 : ℝ := (2331118689 / 10000000000)
noncomputable def tm12863 : ℝ := (-((3047624523 / 5000000000)))
noncomputable def ep12863 : ℝ := (12964687438903891 / 25000000000000000000)
noncomputable def em12863 : ℝ := (19721253056977 / 39062500000000000)
noncomputable def bp12863 : ℝ := (21719253664303529557 / 50000000000000000000)
noncomputable def bm12863 : ℝ := (44407654630120575851 / 100000000000000000000)

theorem positive12863 :
    Eplus aL (agent12863.root+dsL) scalar12863.worldRadius world12863.frame
      agent12863.frame tp12863 ≤ -ep12863 := by
  apply positive_check (eT := (115641163068415896903 / 100000000000000000000)) (y := (37974303472787967527 / 100000000000000000000)) (u := (146190888135081552399 / 100000000000000000000))
  · norm_num [world12863, agent12863, scalar12863, tp12863, tm12863, ep12863, em12863, dsL]
  · norm_num [world12863, agent12863, scalar12863, tp12863, tm12863, ep12863, em12863, dsL]
  · norm_num [world12863, agent12863, scalar12863, tp12863, tm12863, ep12863, em12863, dsL]
  · norm_num [world12863, agent12863, scalar12863, tp12863, tm12863, ep12863, em12863, dsL]
  · norm_num [world12863, agent12863, scalar12863, tp12863, tm12863, ep12863, em12863, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12863, agent12863, tp12863, tm12863, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12863, agent12863, scalar12863, tp12863, tm12863, ep12863, em12863, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12863, agent12863, tp12863, tm12863, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12863, agent12863, scalar12863, tp12863, tm12863, ep12863, em12863, dsL]

theorem negative12863 :
    Eminus aL (agent12863.root+dsL) scalar12863.worldRadius world12863.frame
      agent12863.frame tm12863 ≤ -em12863 := by
  apply negative_check (lo := (34193842120070925137 / 50000000000000000000)) (hi := (2735507369605674011 / 4000000000000000000))
    (y := (-((17915933067182355027 / 25000000000000000000)))) (u := (48839180181487773791 / 100000000000000000000))
  · norm_num [world12863, agent12863, scalar12863, tp12863, tm12863, ep12863, em12863, dsL]
  · norm_num [world12863, agent12863, scalar12863, tp12863, tm12863, ep12863, em12863, dsL]
  · norm_num [world12863, agent12863, scalar12863, tp12863, tm12863, ep12863, em12863, dsL]
  · norm_num [world12863, agent12863, scalar12863, tp12863, tm12863, ep12863, em12863, dsL]
  · norm_num [world12863, agent12863, scalar12863, tp12863, tm12863, ep12863, em12863, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12863, agent12863, tp12863, tm12863, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12863, agent12863, tp12863, tm12863, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12863, agent12863, scalar12863, tp12863, tm12863, ep12863, em12863, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12863, agent12863, tp12863, tm12863, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12863, agent12863, scalar12863, tp12863, tm12863, ep12863, em12863, dsL]

theorem tails12863 :
    exp (-((12863:ℝ)*ep12863)) ≤ scalar12863.upperTail ∧
    exp (-((12863:ℝ)*em12863)) ≤ scalar12863.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12863:ℝ)) (by norm_num [ep12863]) ?_)
      (show bp12863^8 ≤ scalar12863.upperTail by norm_num [bp12863, scalar12863])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12863, bp12863, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12863:ℝ)) (by norm_num [em12863]) ?_)
      (show bm12863^8 ≤ scalar12863.lowerTail by norm_num [bm12863, scalar12863])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12863, bm12863, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12863 :
    agent12863.root+dsL+scalar12863.worldRadius < √(1/100/aL) ∧
    2*(agent12863.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12863, agent12863, scalar12863, tp12863, tm12863, ep12863, em12863, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12863, agent12863, scalar12863, tp12863, tm12863, ep12863, em12863, dsL]

noncomputable def master12863 : MasterCertificate 12863 world12863 agent12863 :=
  master scalar12863 dsL tp12863 tm12863 ep12863 em12863
    (by norm_num [dsL]) (by norm_num [tp12863]) (by norm_num [tm12863])
    (by norm_num [ep12863]) (by norm_num [em12863])
    positive12863 negative12863 tails12863.1 tails12863.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12863.1 tailGuards12863.2

theorem preserves12863 : master12863.toScalarCertificate = scalar12863 := rfl

noncomputable def tp12864 : ℝ := (2331198389 / 10000000000)
noncomputable def tm12864 : ℝ := (-((609541929 / 1000000000)))
noncomputable def ep12864 : ℝ := (51861177503382103 / 100000000000000000000)
noncomputable def em12864 : ℝ := (25244240083248237 / 50000000000000000000)
noncomputable def bp12864 : ℝ := (2171699798454625933 / 5000000000000000000)
noncomputable def bm12864 : ℝ := (22201686275532924551 / 50000000000000000000)

theorem positive12864 :
    Eplus aL (agent12864.root+dsL) scalar12864.worldRadius world12864.frame
      agent12864.frame tp12864 ≤ -ep12864 := by
  apply positive_check (eT := (57820687014638238911 / 50000000000000000000)) (y := (3797503676524039403 / 10000000000000000000)) (u := (146191960145760864121 / 100000000000000000000))
  · norm_num [world12864, agent12864, scalar12864, tp12864, tm12864, ep12864, em12864, dsL]
  · norm_num [world12864, agent12864, scalar12864, tp12864, tm12864, ep12864, em12864, dsL]
  · norm_num [world12864, agent12864, scalar12864, tp12864, tm12864, ep12864, em12864, dsL]
  · norm_num [world12864, agent12864, scalar12864, tp12864, tm12864, ep12864, em12864, dsL]
  · norm_num [world12864, agent12864, scalar12864, tp12864, tm12864, ep12864, em12864, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12864, agent12864, tp12864, tm12864, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12864, agent12864, scalar12864, tp12864, tm12864, ep12864, em12864, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12864, agent12864, tp12864, tm12864, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12864, agent12864, scalar12864, tp12864, tm12864, ep12864, em12864, dsL]

theorem negative12864 :
    Eminus aL (agent12864.root+dsL) scalar12864.worldRadius world12864.frame
      agent12864.frame tm12864 ≤ -em12864 := by
  apply negative_check (lo := (68387520673914207409 / 100000000000000000000)) (hi := (6838752067391420741 / 10000000000000000000))
    (y := (-((35831869947073568587 / 50000000000000000000)))) (u := (9767835291459283471 / 20000000000000000000))
  · norm_num [world12864, agent12864, scalar12864, tp12864, tm12864, ep12864, em12864, dsL]
  · norm_num [world12864, agent12864, scalar12864, tp12864, tm12864, ep12864, em12864, dsL]
  · norm_num [world12864, agent12864, scalar12864, tp12864, tm12864, ep12864, em12864, dsL]
  · norm_num [world12864, agent12864, scalar12864, tp12864, tm12864, ep12864, em12864, dsL]
  · norm_num [world12864, agent12864, scalar12864, tp12864, tm12864, ep12864, em12864, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12864, agent12864, tp12864, tm12864, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12864, agent12864, tp12864, tm12864, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12864, agent12864, scalar12864, tp12864, tm12864, ep12864, em12864, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12864, agent12864, tp12864, tm12864, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12864, agent12864, scalar12864, tp12864, tm12864, ep12864, em12864, dsL]

theorem tails12864 :
    exp (-((12864:ℝ)*ep12864)) ≤ scalar12864.upperTail ∧
    exp (-((12864:ℝ)*em12864)) ≤ scalar12864.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12864:ℝ)) (by norm_num [ep12864]) ?_)
      (show bp12864^8 ≤ scalar12864.upperTail by norm_num [bp12864, scalar12864])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12864, bp12864, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12864:ℝ)) (by norm_num [em12864]) ?_)
      (show bm12864^8 ≤ scalar12864.lowerTail by norm_num [bm12864, scalar12864])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12864, bm12864, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12864 :
    agent12864.root+dsL+scalar12864.worldRadius < √(1/100/aL) ∧
    2*(agent12864.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12864, agent12864, scalar12864, tp12864, tm12864, ep12864, em12864, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12864, agent12864, scalar12864, tp12864, tm12864, ep12864, em12864, dsL]

noncomputable def master12864 : MasterCertificate 12864 world12864 agent12864 :=
  master scalar12864 dsL tp12864 tm12864 ep12864 em12864
    (by norm_num [dsL]) (by norm_num [tp12864]) (by norm_num [tm12864])
    (by norm_num [ep12864]) (by norm_num [em12864])
    positive12864 negative12864 tails12864.1 tails12864.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12864.1 tailGuards12864.2

theorem preserves12864 : master12864.toScalarCertificate = scalar12864 := rfl

noncomputable def tp12865 : ℝ := (2331278143 / 10000000000)
noncomputable def tm12865 : ℝ := (-((1219117873 / 2000000000)))
noncomputable def ep12865 : ℝ := (25931802052723579 / 50000000000000000000)
noncomputable def em12865 : ℝ := (25245275726939553 / 50000000000000000000)
noncomputable def bp12865 : ℝ := (43429485614679557297 / 100000000000000000000)
noncomputable def bm12865 : ℝ := (44399091406907284541 / 100000000000000000000)

theorem positive12865 :
    Eplus aL (agent12865.root+dsL) scalar12865.worldRadius world12865.frame
      agent12865.frame tp12865 ≤ -ep12865 := by
  apply positive_check (eT := (14455198176551375901 / 12500000000000000000)) (y := (37975771294666203517 / 100000000000000000000)) (u := (146193033972670084899 / 100000000000000000000))
  · norm_num [world12865, agent12865, scalar12865, tp12865, tm12865, ep12865, em12865, dsL]
  · norm_num [world12865, agent12865, scalar12865, tp12865, tm12865, ep12865, em12865, dsL]
  · norm_num [world12865, agent12865, scalar12865, tp12865, tm12865, ep12865, em12865, dsL]
  · norm_num [world12865, agent12865, scalar12865, tp12865, tm12865, ep12865, em12865, dsL]
  · norm_num [world12865, agent12865, scalar12865, tp12865, tm12865, ep12865, em12865, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12865, agent12865, tp12865, tm12865, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12865, agent12865, scalar12865, tp12865, tm12865, ep12865, em12865, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12865, agent12865, tp12865, tm12865, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12865, agent12865, scalar12865, tp12865, tm12865, ep12865, em12865, dsL]

theorem negative12865 :
    Eminus aL (agent12865.root+dsL) scalar12865.worldRadius world12865.frame
      agent12865.frame tm12865 ≤ -em12865 := by
  apply negative_check (lo := (8548419721383655073 / 12500000000000000000)) (hi := (13677471554213848117 / 20000000000000000000))
    (y := (-((71663746398226878189 / 100000000000000000000)))) (u := (48839173280757539019 / 100000000000000000000))
  · norm_num [world12865, agent12865, scalar12865, tp12865, tm12865, ep12865, em12865, dsL]
  · norm_num [world12865, agent12865, scalar12865, tp12865, tm12865, ep12865, em12865, dsL]
  · norm_num [world12865, agent12865, scalar12865, tp12865, tm12865, ep12865, em12865, dsL]
  · norm_num [world12865, agent12865, scalar12865, tp12865, tm12865, ep12865, em12865, dsL]
  · norm_num [world12865, agent12865, scalar12865, tp12865, tm12865, ep12865, em12865, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12865, agent12865, tp12865, tm12865, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12865, agent12865, tp12865, tm12865, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12865, agent12865, scalar12865, tp12865, tm12865, ep12865, em12865, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12865, agent12865, tp12865, tm12865, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12865, agent12865, scalar12865, tp12865, tm12865, ep12865, em12865, dsL]

theorem tails12865 :
    exp (-((12865:ℝ)*ep12865)) ≤ scalar12865.upperTail ∧
    exp (-((12865:ℝ)*em12865)) ≤ scalar12865.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12865:ℝ)) (by norm_num [ep12865]) ?_)
      (show bp12865^8 ≤ scalar12865.upperTail by norm_num [bp12865, scalar12865])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12865, bp12865, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12865:ℝ)) (by norm_num [em12865]) ?_)
      (show bm12865^8 ≤ scalar12865.lowerTail by norm_num [bm12865, scalar12865])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12865, bm12865, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12865 :
    agent12865.root+dsL+scalar12865.worldRadius < √(1/100/aL) ∧
    2*(agent12865.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12865, agent12865, scalar12865, tp12865, tm12865, ep12865, em12865, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12865, agent12865, scalar12865, tp12865, tm12865, ep12865, em12865, dsL]

noncomputable def master12865 : MasterCertificate 12865 world12865 agent12865 :=
  master scalar12865 dsL tp12865 tm12865 ep12865 em12865
    (by norm_num [dsL]) (by norm_num [tp12865]) (by norm_num [tm12865])
    (by norm_num [ep12865]) (by norm_num [em12865])
    positive12865 negative12865 tails12865.1 tails12865.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12865.1 tailGuards12865.2

theorem preserves12865 : master12865.toScalarCertificate = scalar12865 := rfl

noncomputable def tp12866 : ℝ := (1165678907 / 5000000000)
noncomputable def tm12866 : ℝ := (-((3047879689 / 5000000000)))
noncomputable def ep12866 : ℝ := (648325373669811 / 1250000000000000000)
noncomputable def em12866 : ℝ := (50492621978342609 / 100000000000000000000)
noncomputable def bp12866 : ℝ := (43424976033633772567 / 100000000000000000000)
noncomputable def bm12866 : ℝ := (22197405495168591241 / 50000000000000000000)

theorem positive12866 :
    Eplus aL (agent12866.root+dsL) scalar12866.worldRadius world12866.frame
      agent12866.frame tp12866 ≤ -ep12866 := by
  apply positive_check (eT := (1445522452876733173 / 1250000000000000000)) (y := (1519060190642251161 / 4000000000000000000)) (u := (29238821252136203177 / 20000000000000000000))
  · norm_num [world12866, agent12866, scalar12866, tp12866, tm12866, ep12866, em12866, dsL]
  · norm_num [world12866, agent12866, scalar12866, tp12866, tm12866, ep12866, em12866, dsL]
  · norm_num [world12866, agent12866, scalar12866, tp12866, tm12866, ep12866, em12866, dsL]
  · norm_num [world12866, agent12866, scalar12866, tp12866, tm12866, ep12866, em12866, dsL]
  · norm_num [world12866, agent12866, scalar12866, tp12866, tm12866, ep12866, em12866, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12866, agent12866, tp12866, tm12866, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12866, agent12866, scalar12866, tp12866, tm12866, ep12866, em12866, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12866, agent12866, tp12866, tm12866, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12866, agent12866, scalar12866, tp12866, tm12866, ep12866, em12866, dsL]

theorem negative12866 :
    Eminus aL (agent12866.root+dsL) scalar12866.worldRadius world12866.frame
      agent12866.frame tm12866 ≤ -em12866 := by
  apply negative_check (lo := (68387195075534571887 / 100000000000000000000)) (hi := (4274199692220910743 / 6250000000000000000))
    (y := (-((71663753229851281849 / 100000000000000000000)))) (u := (24419584972124386297 / 50000000000000000000))
  · norm_num [world12866, agent12866, scalar12866, tp12866, tm12866, ep12866, em12866, dsL]
  · norm_num [world12866, agent12866, scalar12866, tp12866, tm12866, ep12866, em12866, dsL]
  · norm_num [world12866, agent12866, scalar12866, tp12866, tm12866, ep12866, em12866, dsL]
  · norm_num [world12866, agent12866, scalar12866, tp12866, tm12866, ep12866, em12866, dsL]
  · norm_num [world12866, agent12866, scalar12866, tp12866, tm12866, ep12866, em12866, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12866, agent12866, tp12866, tm12866, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12866, agent12866, tp12866, tm12866, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12866, agent12866, scalar12866, tp12866, tm12866, ep12866, em12866, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12866, agent12866, tp12866, tm12866, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12866, agent12866, scalar12866, tp12866, tm12866, ep12866, em12866, dsL]

theorem tails12866 :
    exp (-((12866:ℝ)*ep12866)) ≤ scalar12866.upperTail ∧
    exp (-((12866:ℝ)*em12866)) ≤ scalar12866.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12866:ℝ)) (by norm_num [ep12866]) ?_)
      (show bp12866^8 ≤ scalar12866.upperTail by norm_num [bp12866, scalar12866])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12866, bp12866, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12866:ℝ)) (by norm_num [em12866]) ?_)
      (show bm12866^8 ≤ scalar12866.lowerTail by norm_num [bm12866, scalar12866])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12866, bm12866, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12866 :
    agent12866.root+dsL+scalar12866.worldRadius < √(1/100/aL) ∧
    2*(agent12866.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12866, agent12866, scalar12866, tp12866, tm12866, ep12866, em12866, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12866, agent12866, scalar12866, tp12866, tm12866, ep12866, em12866, dsL]

noncomputable def master12866 : MasterCertificate 12866 world12866 agent12866 :=
  master scalar12866 dsL tp12866 tm12866 ep12866 em12866
    (by norm_num [dsL]) (by norm_num [tp12866]) (by norm_num [tm12866])
    (by norm_num [ep12866]) (by norm_num [em12866])
    positive12866 negative12866 tails12866.1 tails12866.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12866.1 tailGuards12866.2

theorem preserves12866 : master12866.toScalarCertificate = scalar12866 := rfl

noncomputable def tp12867 : ℝ := (2331437439 / 10000000000)
noncomputable def tm12867 : ℝ := (-((3047964539 / 5000000000)))
noncomputable def ep12867 : ℝ := (6483556817019723 / 12500000000000000000)
noncomputable def em12867 : ℝ := (3155918215609069 / 6250000000000000000)
noncomputable def bp12867 : ℝ := (8684093491509541637 / 20000000000000000000)
noncomputable def bm12867 : ℝ := (44390531508503188657 / 100000000000000000000)

theorem positive12867 :
    Eplus aL (agent12867.root+dsL) scalar12867.worldRadius world12867.frame
      agent12867.frame tp12867 ≤ -ep12867 := by
  apply positive_check (eT := (115642006749215218833 / 100000000000000000000)) (y := (37977237723944138983 / 100000000000000000000)) (u := (29239035561168284501 / 20000000000000000000))
  · norm_num [world12867, agent12867, scalar12867, tp12867, tm12867, ep12867, em12867, dsL]
  · norm_num [world12867, agent12867, scalar12867, tp12867, tm12867, ep12867, em12867, dsL]
  · norm_num [world12867, agent12867, scalar12867, tp12867, tm12867, ep12867, em12867, dsL]
  · norm_num [world12867, agent12867, scalar12867, tp12867, tm12867, ep12867, em12867, dsL]
  · norm_num [world12867, agent12867, scalar12867, tp12867, tm12867, ep12867, em12867, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12867, agent12867, tp12867, tm12867, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12867, agent12867, scalar12867, tp12867, tm12867, ep12867, em12867, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12867, agent12867, tp12867, tm12867, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12867, agent12867, scalar12867, tp12867, tm12867, ep12867, em12867, dsL]

theorem negative12867 :
    Eminus aL (agent12867.root+dsL) scalar12867.worldRadius world12867.frame
      agent12867.frame tm12867 ≤ -em12867 := by
  apply negative_check (lo := (68387033657265614393 / 100000000000000000000)) (hi := (34193516828632807197 / 50000000000000000000))
    (y := (-((71663757548217658883 / 100000000000000000000)))) (u := (24419583917597262219 / 50000000000000000000))
  · norm_num [world12867, agent12867, scalar12867, tp12867, tm12867, ep12867, em12867, dsL]
  · norm_num [world12867, agent12867, scalar12867, tp12867, tm12867, ep12867, em12867, dsL]
  · norm_num [world12867, agent12867, scalar12867, tp12867, tm12867, ep12867, em12867, dsL]
  · norm_num [world12867, agent12867, scalar12867, tp12867, tm12867, ep12867, em12867, dsL]
  · norm_num [world12867, agent12867, scalar12867, tp12867, tm12867, ep12867, em12867, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12867, agent12867, tp12867, tm12867, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12867, agent12867, tp12867, tm12867, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12867, agent12867, scalar12867, tp12867, tm12867, ep12867, em12867, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12867, agent12867, tp12867, tm12867, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12867, agent12867, scalar12867, tp12867, tm12867, ep12867, em12867, dsL]

theorem tails12867 :
    exp (-((12867:ℝ)*ep12867)) ≤ scalar12867.upperTail ∧
    exp (-((12867:ℝ)*em12867)) ≤ scalar12867.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12867:ℝ)) (by norm_num [ep12867]) ?_)
      (show bp12867^8 ≤ scalar12867.upperTail by norm_num [bp12867, scalar12867])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12867, bp12867, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12867:ℝ)) (by norm_num [em12867]) ?_)
      (show bm12867^8 ≤ scalar12867.lowerTail by norm_num [bm12867, scalar12867])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12867, bm12867, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12867 :
    agent12867.root+dsL+scalar12867.worldRadius < √(1/100/aL) ∧
    2*(agent12867.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12867, agent12867, scalar12867, tp12867, tm12867, ep12867, em12867, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12867, agent12867, scalar12867, tp12867, tm12867, ep12867, em12867, dsL]

noncomputable def master12867 : MasterCertificate 12867 world12867 agent12867 :=
  master scalar12867 dsL tp12867 tm12867 ep12867 em12867
    (by norm_num [dsL]) (by norm_num [tp12867]) (by norm_num [tm12867])
    (by norm_num [ep12867]) (by norm_num [em12867])
    positive12867 negative12867 tails12867.1 tails12867.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12867.1 tailGuards12867.2

theorem preserves12867 : master12867.toScalarCertificate = scalar12867 := rfl

noncomputable def tp12868 : ℝ := (1165758507 / 5000000000)
noncomputable def tm12868 : ℝ := (-((152402473 / 250000000)))
noncomputable def ep12868 : ℝ := (51870877415377489 / 100000000000000000000)
noncomputable def em12868 : ℝ := (50496759279172817 / 100000000000000000000)
noncomputable def bp12868 : ℝ := (43415960317821953809 / 100000000000000000000)
noncomputable def bm12868 : ℝ := (44386253381846509063 / 100000000000000000000)

theorem positive12868 :
    Eplus aL (agent12868.root+dsL) scalar12868.worldRadius world12868.frame
      agent12868.frame tp12868 ≤ -ep12868 := by
  apply positive_check (eT := (115642216940860032313 / 100000000000000000000)) (y := (37977970299438498051 / 100000000000000000000)) (u := (7309812439990543883 / 5000000000000000000))
  · norm_num [world12868, agent12868, scalar12868, tp12868, tm12868, ep12868, em12868, dsL]
  · norm_num [world12868, agent12868, scalar12868, tp12868, tm12868, ep12868, em12868, dsL]
  · norm_num [world12868, agent12868, scalar12868, tp12868, tm12868, ep12868, em12868, dsL]
  · norm_num [world12868, agent12868, scalar12868, tp12868, tm12868, ep12868, em12868, dsL]
  · norm_num [world12868, agent12868, scalar12868, tp12868, tm12868, ep12868, em12868, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12868, agent12868, tp12868, tm12868, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12868, agent12868, scalar12868, tp12868, tm12868, ep12868, em12868, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12868, agent12868, tp12868, tm12868, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12868, agent12868, scalar12868, tp12868, tm12868, ep12868, em12868, dsL]

theorem negative12868 :
    Eminus aL (agent12868.root+dsL) scalar12868.worldRadius world12868.frame
      agent12868.frame tm12868 ≤ -em12868 := by
  apply negative_check (lo := (34193435788278155129 / 50000000000000000000)) (hi := (68386871576556310259 / 100000000000000000000))
    (y := (-((35831881954506499913 / 50000000000000000000)))) (u := (24419582364317555511 / 50000000000000000000))
  · norm_num [world12868, agent12868, scalar12868, tp12868, tm12868, ep12868, em12868, dsL]
  · norm_num [world12868, agent12868, scalar12868, tp12868, tm12868, ep12868, em12868, dsL]
  · norm_num [world12868, agent12868, scalar12868, tp12868, tm12868, ep12868, em12868, dsL]
  · norm_num [world12868, agent12868, scalar12868, tp12868, tm12868, ep12868, em12868, dsL]
  · norm_num [world12868, agent12868, scalar12868, tp12868, tm12868, ep12868, em12868, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12868, agent12868, tp12868, tm12868, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12868, agent12868, tp12868, tm12868, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12868, agent12868, scalar12868, tp12868, tm12868, ep12868, em12868, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12868, agent12868, tp12868, tm12868, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12868, agent12868, scalar12868, tp12868, tm12868, ep12868, em12868, dsL]

theorem tails12868 :
    exp (-((12868:ℝ)*ep12868)) ≤ scalar12868.upperTail ∧
    exp (-((12868:ℝ)*em12868)) ≤ scalar12868.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12868:ℝ)) (by norm_num [ep12868]) ?_)
      (show bp12868^8 ≤ scalar12868.upperTail by norm_num [bp12868, scalar12868])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12868, bp12868, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12868:ℝ)) (by norm_num [em12868]) ?_)
      (show bm12868^8 ≤ scalar12868.lowerTail by norm_num [bm12868, scalar12868])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12868, bm12868, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12868 :
    agent12868.root+dsL+scalar12868.worldRadius < √(1/100/aL) ∧
    2*(agent12868.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12868, agent12868, scalar12868, tp12868, tm12868, ep12868, em12868, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12868, agent12868, scalar12868, tp12868, tm12868, ep12868, em12868, dsL]

noncomputable def master12868 : MasterCertificate 12868 world12868 agent12868 :=
  master scalar12868 dsL tp12868 tm12868 ep12868 em12868
    (by norm_num [dsL]) (by norm_num [tp12868]) (by norm_num [tm12868])
    (by norm_num [ep12868]) (by norm_num [em12868])
    positive12868 negative12868 tails12868.1 tails12868.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12868.1 tailGuards12868.2

theorem preserves12868 : master12868.toScalarCertificate = scalar12868 := rfl

noncomputable def tp12869 : ℝ := (2331596557 / 10000000000)
noncomputable def tm12869 : ℝ := (-((152406717 / 250000000)))
noncomputable def ep12869 : ℝ := (51873299454021119 / 100000000000000000000)
noncomputable def em12869 : ℝ := (50498826315473721 / 100000000000000000000)
noncomputable def bp12869 : ℝ := (2713215873124550001 / 6250000000000000000)
noncomputable def bm12869 : ℝ := (1775279040172078333 / 4000000000000000000)

theorem positive12869 :
    Eplus aL (agent12869.root+dsL) scalar12869.worldRadius world12869.frame
      agent12869.frame tp12869 ≤ -ep12869 := by
  apply positive_check (eT := (2312848538695887 / 2000000000000000)) (y := (7595740521423280399 / 20000000000000000000)) (u := (29239463882017144413 / 20000000000000000000))
  · norm_num [world12869, agent12869, scalar12869, tp12869, tm12869, ep12869, em12869, dsL]
  · norm_num [world12869, agent12869, scalar12869, tp12869, tm12869, ep12869, em12869, dsL]
  · norm_num [world12869, agent12869, scalar12869, tp12869, tm12869, ep12869, em12869, dsL]
  · norm_num [world12869, agent12869, scalar12869, tp12869, tm12869, ep12869, em12869, dsL]
  · norm_num [world12869, agent12869, scalar12869, tp12869, tm12869, ep12869, em12869, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12869, agent12869, tp12869, tm12869, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12869, agent12869, scalar12869, tp12869, tm12869, ep12869, em12869, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12869, agent12869, tp12869, tm12869, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12869, agent12869, scalar12869, tp12869, tm12869, ep12869, em12869, dsL]

theorem negative12869 :
    Eminus aL (agent12869.root+dsL) scalar12869.worldRadius world12869.frame
      agent12869.frame tm12869 ≤ -em12869 := by
  apply negative_check (lo := (68386709788364643609 / 100000000000000000000)) (hi := (6838670978836464361 / 10000000000000000000))
    (y := (-((17915942497860763759 / 25000000000000000000)))) (u := (48839161758027167197 / 100000000000000000000))
  · norm_num [world12869, agent12869, scalar12869, tp12869, tm12869, ep12869, em12869, dsL]
  · norm_num [world12869, agent12869, scalar12869, tp12869, tm12869, ep12869, em12869, dsL]
  · norm_num [world12869, agent12869, scalar12869, tp12869, tm12869, ep12869, em12869, dsL]
  · norm_num [world12869, agent12869, scalar12869, tp12869, tm12869, ep12869, em12869, dsL]
  · norm_num [world12869, agent12869, scalar12869, tp12869, tm12869, ep12869, em12869, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12869, agent12869, tp12869, tm12869, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12869, agent12869, tp12869, tm12869, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12869, agent12869, scalar12869, tp12869, tm12869, ep12869, em12869, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12869, agent12869, tp12869, tm12869, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12869, agent12869, scalar12869, tp12869, tm12869, ep12869, em12869, dsL]

theorem tails12869 :
    exp (-((12869:ℝ)*ep12869)) ≤ scalar12869.upperTail ∧
    exp (-((12869:ℝ)*em12869)) ≤ scalar12869.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12869:ℝ)) (by norm_num [ep12869]) ?_)
      (show bp12869^8 ≤ scalar12869.upperTail by norm_num [bp12869, scalar12869])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12869, bp12869, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12869:ℝ)) (by norm_num [em12869]) ?_)
      (show bm12869^8 ≤ scalar12869.lowerTail by norm_num [bm12869, scalar12869])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12869, bm12869, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12869 :
    agent12869.root+dsL+scalar12869.worldRadius < √(1/100/aL) ∧
    2*(agent12869.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12869, agent12869, scalar12869, tp12869, tm12869, ep12869, em12869, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12869, agent12869, scalar12869, tp12869, tm12869, ep12869, em12869, dsL]

noncomputable def master12869 : MasterCertificate 12869 world12869 agent12869 :=
  master scalar12869 dsL tp12869 tm12869 ep12869 em12869
    (by norm_num [dsL]) (by norm_num [tp12869]) (by norm_num [tm12869])
    (by norm_num [ep12869]) (by norm_num [em12869])
    positive12869 negative12869 tails12869.1 tails12869.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12869.1 tailGuards12869.2

theorem preserves12869 : master12869.toScalarCertificate = scalar12869 := rfl

noncomputable def tp12870 : ℝ := (2331749049 / 10000000000)
noncomputable def tm12870 : ℝ := (-((1219331803 / 2000000000)))
noncomputable def ep12870 : ℝ := (51877106412500153 / 100000000000000000000)
noncomputable def em12870 : ℝ := (12625600978330707 / 25000000000000000000)
noncomputable def bp12870 : ℝ := (4340598073547526801 / 10000000000000000000)
noncomputable def bm12870 : ℝ := (2218831019661156617 / 5000000000000000000)

theorem positive12870 :
    Eplus aL (agent12870.root+dsL) scalar12870.worldRadius world12870.frame
      agent12870.frame tp12870 ≤ -ep12870 := by
  apply positive_check (eT := (115643162783896080003 / 100000000000000000000)) (y := (37978715387628027821 / 100000000000000000000)) (u := (146197338094852319921 / 100000000000000000000))
  · norm_num [world12870, agent12870, scalar12870, tp12870, tm12870, ep12870, em12870, dsL]
  · norm_num [world12870, agent12870, scalar12870, tp12870, tm12870, ep12870, em12870, dsL]
  · norm_num [world12870, agent12870, scalar12870, tp12870, tm12870, ep12870, em12870, dsL]
  · norm_num [world12870, agent12870, scalar12870, tp12870, tm12870, ep12870, em12870, dsL]
  · norm_num [world12870, agent12870, scalar12870, tp12870, tm12870, ep12870, em12870, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12870, agent12870, tp12870, tm12870, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12870, agent12870, scalar12870, tp12870, tm12870, ep12870, em12870, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12870, agent12870, tp12870, tm12870, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12870, agent12870, scalar12870, tp12870, tm12870, ep12870, em12870, dsL]

theorem negative12870 :
    Eminus aL (agent12870.root+dsL) scalar12870.worldRadius world12870.frame
      agent12870.frame tm12870 ≤ -em12870 := by
  apply negative_check (lo := (68385607733734651423 / 100000000000000000000)) (hi := (2137050241679207857 / 3125000000000000000))
    (y := (-((35830943788615362731 / 50000000000000000000)))) (u := (48840081122002374849 / 100000000000000000000))
  · norm_num [world12870, agent12870, scalar12870, tp12870, tm12870, ep12870, em12870, dsL]
  · norm_num [world12870, agent12870, scalar12870, tp12870, tm12870, ep12870, em12870, dsL]
  · norm_num [world12870, agent12870, scalar12870, tp12870, tm12870, ep12870, em12870, dsL]
  · norm_num [world12870, agent12870, scalar12870, tp12870, tm12870, ep12870, em12870, dsL]
  · norm_num [world12870, agent12870, scalar12870, tp12870, tm12870, ep12870, em12870, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12870, agent12870, tp12870, tm12870, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12870, agent12870, tp12870, tm12870, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12870, agent12870, scalar12870, tp12870, tm12870, ep12870, em12870, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12870, agent12870, tp12870, tm12870, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12870, agent12870, scalar12870, tp12870, tm12870, ep12870, em12870, dsL]

theorem tails12870 :
    exp (-((12870:ℝ)*ep12870)) ≤ scalar12870.upperTail ∧
    exp (-((12870:ℝ)*em12870)) ≤ scalar12870.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12870:ℝ)) (by norm_num [ep12870]) ?_)
      (show bp12870^8 ≤ scalar12870.upperTail by norm_num [bp12870, scalar12870])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12870, bp12870, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12870:ℝ)) (by norm_num [em12870]) ?_)
      (show bm12870^8 ≤ scalar12870.lowerTail by norm_num [bm12870, scalar12870])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12870, bm12870, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12870 :
    agent12870.root+dsL+scalar12870.worldRadius < √(1/100/aL) ∧
    2*(agent12870.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12870, agent12870, scalar12870, tp12870, tm12870, ep12870, em12870, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12870, agent12870, scalar12870, tp12870, tm12870, ep12870, em12870, dsL]

noncomputable def master12870 : MasterCertificate 12870 world12870 agent12870 :=
  master scalar12870 dsL tp12870 tm12870 ep12870 em12870
    (by norm_num [dsL]) (by norm_num [tp12870]) (by norm_num [tm12870])
    (by norm_num [ep12870]) (by norm_num [em12870])
    positive12870 negative12870 tails12870.1 tails12870.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12870.1 tailGuards12870.2

theorem preserves12870 : master12870.toScalarCertificate = scalar12870 := rfl

noncomputable def tp12871 : ℝ := (2331828521 / 10000000000)
noncomputable def tm12871 : ℝ := (-((1219365689 / 2000000000)))
noncomputable def ep12871 : ℝ := (25939762665867607 / 50000000000000000000)
noncomputable def em12871 : ℝ := (50504468085382197 / 100000000000000000000)
noncomputable def bp12871 : ℝ := (1736059080037840719 / 4000000000000000000)
noncomputable def bm12871 : ℝ := (5546543180796443709 / 12500000000000000000)

theorem positive12871 :
    Eplus aL (agent12871.root+dsL) scalar12871.worldRadius world12871.frame
      agent12871.frame tp12871 ≤ -ep12871 := by
  apply positive_check (eT := (23128674464313770909 / 20000000000000000000)) (y := (18989723580099409429 / 50000000000000000000)) (u := (14619840793078610287 / 10000000000000000000))
  · norm_num [world12871, agent12871, scalar12871, tp12871, tm12871, ep12871, em12871, dsL]
  · norm_num [world12871, agent12871, scalar12871, tp12871, tm12871, ep12871, em12871, dsL]
  · norm_num [world12871, agent12871, scalar12871, tp12871, tm12871, ep12871, em12871, dsL]
  · norm_num [world12871, agent12871, scalar12871, tp12871, tm12871, ep12871, em12871, dsL]
  · norm_num [world12871, agent12871, scalar12871, tp12871, tm12871, ep12871, em12871, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12871, agent12871, tp12871, tm12871, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12871, agent12871, scalar12871, tp12871, tm12871, ep12871, em12871, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12871, agent12871, tp12871, tm12871, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12871, agent12871, scalar12871, tp12871, tm12871, ep12871, em12871, dsL]

theorem negative12871 :
    Eminus aL (agent12871.root+dsL) scalar12871.worldRadius world12871.frame
      agent12871.frame tm12871 ≤ -em12871 := by
  apply negative_check (lo := (2735417890425202267 / 4000000000000000000)) (hi := (17096361815157514169 / 25000000000000000000))
    (y := (-((71661891550681694409 / 100000000000000000000)))) (u := (48840079181365736827 / 100000000000000000000))
  · norm_num [world12871, agent12871, scalar12871, tp12871, tm12871, ep12871, em12871, dsL]
  · norm_num [world12871, agent12871, scalar12871, tp12871, tm12871, ep12871, em12871, dsL]
  · norm_num [world12871, agent12871, scalar12871, tp12871, tm12871, ep12871, em12871, dsL]
  · norm_num [world12871, agent12871, scalar12871, tp12871, tm12871, ep12871, em12871, dsL]
  · norm_num [world12871, agent12871, scalar12871, tp12871, tm12871, ep12871, em12871, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12871, agent12871, tp12871, tm12871, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12871, agent12871, tp12871, tm12871, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12871, agent12871, scalar12871, tp12871, tm12871, ep12871, em12871, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12871, agent12871, tp12871, tm12871, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12871, agent12871, scalar12871, tp12871, tm12871, ep12871, em12871, dsL]

theorem tails12871 :
    exp (-((12871:ℝ)*ep12871)) ≤ scalar12871.upperTail ∧
    exp (-((12871:ℝ)*em12871)) ≤ scalar12871.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12871:ℝ)) (by norm_num [ep12871]) ?_)
      (show bp12871^8 ≤ scalar12871.upperTail by norm_num [bp12871, scalar12871])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12871, bp12871, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12871:ℝ)) (by norm_num [em12871]) ?_)
      (show bm12871^8 ≤ scalar12871.lowerTail by norm_num [bm12871, scalar12871])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12871, bm12871, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12871 :
    agent12871.root+dsL+scalar12871.worldRadius < √(1/100/aL) ∧
    2*(agent12871.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12871, agent12871, scalar12871, tp12871, tm12871, ep12871, em12871, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12871, agent12871, scalar12871, tp12871, tm12871, ep12871, em12871, dsL]

noncomputable def master12871 : MasterCertificate 12871 world12871 agent12871 :=
  master scalar12871 dsL tp12871 tm12871 ep12871 em12871
    (by norm_num [dsL]) (by norm_num [tp12871]) (by norm_num [tm12871])
    (by norm_num [ep12871]) (by norm_num [em12871])
    positive12871 negative12871 tails12871.1 tails12871.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12871.1 tailGuards12871.2

theorem preserves12871 : master12871.toScalarCertificate = scalar12871 := rfl

noncomputable def tp12872 : ℝ := (466381593 / 2000000000)
noncomputable def tm12872 : ℝ := (-((6096997917 / 10000000000)))
noncomputable def ep12872 : ℝ := (6485242948128599 / 12500000000000000000)
noncomputable def em12872 : ℝ := (25253265824163957 / 50000000000000000000)
noncomputable def bp12872 : ℝ := (8679394787256213459 / 20000000000000000000)
noncomputable def bm12872 : ℝ := (44368071117216859883 / 100000000000000000000)

theorem positive12872 :
    Eplus aL (agent12872.root+dsL) scalar12872.worldRadius world12872.frame
      agent12872.frame tp12872 ≤ -ep12872 := by
  apply positive_check (eT := (57821790845198758239 / 50000000000000000000)) (y := (18990089342236469051 / 50000000000000000000)) (u := (146199477411540243337 / 100000000000000000000))
  · norm_num [world12872, agent12872, scalar12872, tp12872, tm12872, ep12872, em12872, dsL]
  · norm_num [world12872, agent12872, scalar12872, tp12872, tm12872, ep12872, em12872, dsL]
  · norm_num [world12872, agent12872, scalar12872, tp12872, tm12872, ep12872, em12872, dsL]
  · norm_num [world12872, agent12872, scalar12872, tp12872, tm12872, ep12872, em12872, dsL]
  · norm_num [world12872, agent12872, scalar12872, tp12872, tm12872, ep12872, em12872, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12872, agent12872, tp12872, tm12872, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12872, agent12872, scalar12872, tp12872, tm12872, ep12872, em12872, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12872, agent12872, tp12872, tm12872, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12872, agent12872, scalar12872, tp12872, tm12872, ep12872, em12872, dsL]

theorem negative12872 :
    Eminus aL (agent12872.root+dsL) scalar12872.worldRadius world12872.frame
      agent12872.frame tm12872 ≤ -em12872 := by
  apply negative_check (lo := (68385286551421329041 / 100000000000000000000)) (hi := (34192643275710664521 / 50000000000000000000))
    (y := (-((71661896567951096351 / 100000000000000000000)))) (u := (48840076730927449649 / 100000000000000000000))
  · norm_num [world12872, agent12872, scalar12872, tp12872, tm12872, ep12872, em12872, dsL]
  · norm_num [world12872, agent12872, scalar12872, tp12872, tm12872, ep12872, em12872, dsL]
  · norm_num [world12872, agent12872, scalar12872, tp12872, tm12872, ep12872, em12872, dsL]
  · norm_num [world12872, agent12872, scalar12872, tp12872, tm12872, ep12872, em12872, dsL]
  · norm_num [world12872, agent12872, scalar12872, tp12872, tm12872, ep12872, em12872, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12872, agent12872, tp12872, tm12872, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12872, agent12872, tp12872, tm12872, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12872, agent12872, scalar12872, tp12872, tm12872, ep12872, em12872, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12872, agent12872, tp12872, tm12872, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12872, agent12872, scalar12872, tp12872, tm12872, ep12872, em12872, dsL]

theorem tails12872 :
    exp (-((12872:ℝ)*ep12872)) ≤ scalar12872.upperTail ∧
    exp (-((12872:ℝ)*em12872)) ≤ scalar12872.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12872:ℝ)) (by norm_num [ep12872]) ?_)
      (show bp12872^8 ≤ scalar12872.upperTail by norm_num [bp12872, scalar12872])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12872, bp12872, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12872:ℝ)) (by norm_num [em12872]) ?_)
      (show bm12872^8 ≤ scalar12872.lowerTail by norm_num [bm12872, scalar12872])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12872, bm12872, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12872 :
    agent12872.root+dsL+scalar12872.worldRadius < √(1/100/aL) ∧
    2*(agent12872.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12872, agent12872, scalar12872, tp12872, tm12872, ep12872, em12872, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12872, agent12872, scalar12872, tp12872, tm12872, ep12872, em12872, dsL]

noncomputable def master12872 : MasterCertificate 12872 world12872 agent12872 :=
  master scalar12872 dsL tp12872 tm12872 ep12872 em12872
    (by norm_num [dsL]) (by norm_num [tp12872]) (by norm_num [tm12872])
    (by norm_num [ep12872]) (by norm_num [em12872])
    positive12872 negative12872 tails12872.1 tails12872.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12872.1 tailGuards12872.2

theorem preserves12872 : master12872.toScalarCertificate = scalar12872 := rfl

noncomputable def tp12873 : ℝ := (2331987347 / 10000000000)
noncomputable def tm12873 : ℝ := (-((3048583689 / 5000000000)))
noncomputable def ep12873 : ℝ := (324277253465573 / 625000000000000000)
noncomputable def em12873 : ℝ := (50508594013131963 / 100000000000000000000)
noncomputable def bp12873 : ℝ := (43392471972911653191 / 100000000000000000000)
noncomputable def bm12873 : ℝ := (2218189891312502319 / 5000000000000000000)

theorem positive12873 :
    Eplus aL (agent12873.root+dsL) scalar12873.worldRadius world12873.frame
      agent12873.frame tp12873 ≤ -ep12873 := by
  apply positive_check (eT := (115643790645312421487 / 100000000000000000000)) (y := (2373806847916093927 / 6250000000000000000)) (u := (36550136490344871617 / 25000000000000000000))
  · norm_num [world12873, agent12873, scalar12873, tp12873, tm12873, ep12873, em12873, dsL]
  · norm_num [world12873, agent12873, scalar12873, tp12873, tm12873, ep12873, em12873, dsL]
  · norm_num [world12873, agent12873, scalar12873, tp12873, tm12873, ep12873, em12873, dsL]
  · norm_num [world12873, agent12873, scalar12873, tp12873, tm12873, ep12873, em12873, dsL]
  · norm_num [world12873, agent12873, scalar12873, tp12873, tm12873, ep12873, em12873, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12873, agent12873, tp12873, tm12873, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12873, agent12873, scalar12873, tp12873, tm12873, ep12873, em12873, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12873, agent12873, tp12873, tm12873, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12873, agent12873, scalar12873, tp12873, tm12873, ep12873, em12873, dsL]

theorem negative12873 :
    Eminus aL (agent12873.root+dsL) scalar12873.worldRadius world12873.frame
      agent12873.frame tm12873 ≤ -em12873 := by
  apply negative_check (lo := (68385125832052781753 / 100000000000000000000)) (hi := (34192562916026390877 / 50000000000000000000))
    (y := (-((35830951137887369313 / 50000000000000000000)))) (u := (24420036971611041327 / 50000000000000000000))
  · norm_num [world12873, agent12873, scalar12873, tp12873, tm12873, ep12873, em12873, dsL]
  · norm_num [world12873, agent12873, scalar12873, tp12873, tm12873, ep12873, em12873, dsL]
  · norm_num [world12873, agent12873, scalar12873, tp12873, tm12873, ep12873, em12873, dsL]
  · norm_num [world12873, agent12873, scalar12873, tp12873, tm12873, ep12873, em12873, dsL]
  · norm_num [world12873, agent12873, scalar12873, tp12873, tm12873, ep12873, em12873, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12873, agent12873, tp12873, tm12873, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12873, agent12873, tp12873, tm12873, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12873, agent12873, scalar12873, tp12873, tm12873, ep12873, em12873, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12873, agent12873, tp12873, tm12873, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12873, agent12873, scalar12873, tp12873, tm12873, ep12873, em12873, dsL]

theorem tails12873 :
    exp (-((12873:ℝ)*ep12873)) ≤ scalar12873.upperTail ∧
    exp (-((12873:ℝ)*em12873)) ≤ scalar12873.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12873:ℝ)) (by norm_num [ep12873]) ?_)
      (show bp12873^8 ≤ scalar12873.upperTail by norm_num [bp12873, scalar12873])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12873, bp12873, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12873:ℝ)) (by norm_num [em12873]) ?_)
      (show bm12873^8 ≤ scalar12873.lowerTail by norm_num [bm12873, scalar12873])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12873, bm12873, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12873 :
    agent12873.root+dsL+scalar12873.worldRadius < √(1/100/aL) ∧
    2*(agent12873.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12873, agent12873, scalar12873, tp12873, tm12873, ep12873, em12873, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12873, agent12873, scalar12873, tp12873, tm12873, ep12873, em12873, dsL]

noncomputable def master12873 : MasterCertificate 12873 world12873 agent12873 :=
  master scalar12873 dsL tp12873 tm12873 ep12873 em12873
    (by norm_num [dsL]) (by norm_num [tp12873]) (by norm_num [tm12873])
    (by norm_num [ep12873]) (by norm_num [em12873])
    positive12873 negative12873 tails12873.1 tails12873.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12873.1 tailGuards12873.2

theorem preserves12873 : master12873.toScalarCertificate = scalar12873 := rfl

noncomputable def tp12874 : ℝ := (2332066683 / 10000000000)
noncomputable def tm12874 : ℝ := (-((3048668251 / 5000000000)))
noncomputable def ep12874 : ℝ := (25943387795361127 / 50000000000000000000)
noncomputable def em12874 : ℝ := (631383181953483 / 1250000000000000000)
noncomputable def bp12874 : ℝ := (43387971564226653 / 100000000000000000)
noncomputable def bm12874 : ℝ := (11089881504637491851 / 25000000000000000000)

theorem positive12874 :
    Eplus aL (agent12874.root+dsL) scalar12874.worldRadius world12874.frame
      agent12874.frame tp12874 ≤ -ep12874 := by
  apply positive_check (eT := (115643999301666551083 / 100000000000000000000)) (y := (4747705023233156889 / 12500000000000000000)) (u := (73100807067276126721 / 50000000000000000000))
  · norm_num [world12874, agent12874, scalar12874, tp12874, tm12874, ep12874, em12874, dsL]
  · norm_num [world12874, agent12874, scalar12874, tp12874, tm12874, ep12874, em12874, dsL]
  · norm_num [world12874, agent12874, scalar12874, tp12874, tm12874, ep12874, em12874, dsL]
  · norm_num [world12874, agent12874, scalar12874, tp12874, tm12874, ep12874, em12874, dsL]
  · norm_num [world12874, agent12874, scalar12874, tp12874, tm12874, ep12874, em12874, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12874, agent12874, tp12874, tm12874, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12874, agent12874, scalar12874, tp12874, tm12874, ep12874, em12874, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12874, agent12874, tp12874, tm12874, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12874, agent12874, scalar12874, tp12874, tm12874, ep12874, em12874, dsL]

theorem negative12874 :
    Eminus aL (agent12874.root+dsL) scalar12874.worldRadius world12874.frame
      agent12874.frame tm12874 ≤ -em12874 := by
  apply negative_check (lo := (1068515101436856963 / 1562500000000000000)) (hi := (68384966491958845633 / 100000000000000000000))
    (y := (-((14332381054304989513 / 20000000000000000000)))) (u := (4884007248009548737 / 10000000000000000000))
  · norm_num [world12874, agent12874, scalar12874, tp12874, tm12874, ep12874, em12874, dsL]
  · norm_num [world12874, agent12874, scalar12874, tp12874, tm12874, ep12874, em12874, dsL]
  · norm_num [world12874, agent12874, scalar12874, tp12874, tm12874, ep12874, em12874, dsL]
  · norm_num [world12874, agent12874, scalar12874, tp12874, tm12874, ep12874, em12874, dsL]
  · norm_num [world12874, agent12874, scalar12874, tp12874, tm12874, ep12874, em12874, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12874, agent12874, tp12874, tm12874, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12874, agent12874, tp12874, tm12874, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12874, agent12874, scalar12874, tp12874, tm12874, ep12874, em12874, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12874, agent12874, tp12874, tm12874, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12874, agent12874, scalar12874, tp12874, tm12874, ep12874, em12874, dsL]

theorem tails12874 :
    exp (-((12874:ℝ)*ep12874)) ≤ scalar12874.upperTail ∧
    exp (-((12874:ℝ)*em12874)) ≤ scalar12874.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12874:ℝ)) (by norm_num [ep12874]) ?_)
      (show bp12874^8 ≤ scalar12874.upperTail by norm_num [bp12874, scalar12874])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12874, bp12874, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12874:ℝ)) (by norm_num [em12874]) ?_)
      (show bm12874^8 ≤ scalar12874.lowerTail by norm_num [bm12874, scalar12874])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12874, bm12874, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12874 :
    agent12874.root+dsL+scalar12874.worldRadius < √(1/100/aL) ∧
    2*(agent12874.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12874, agent12874, scalar12874, tp12874, tm12874, ep12874, em12874, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12874, agent12874, scalar12874, tp12874, tm12874, ep12874, em12874, dsL]

noncomputable def master12874 : MasterCertificate 12874 world12874 agent12874 :=
  master scalar12874 dsL tp12874 tm12874 ep12874 em12874
    (by norm_num [dsL]) (by norm_num [tp12874]) (by norm_num [tm12874])
    (by norm_num [ep12874]) (by norm_num [em12874])
    positive12874 negative12874 tails12874.1 tails12874.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12874.1 tailGuards12874.2

theorem preserves12874 : master12874.toScalarCertificate = scalar12874 := rfl

end BstLean.Part268
