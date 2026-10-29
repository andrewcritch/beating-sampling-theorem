import BstLean.Part261Checker
import BstLean.Part268Scalar23
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12925 : ℝ := (1168221017 / 5000000000)
noncomputable def tm12925 : ℝ := (-((763373827 / 1250000000)))
noncomputable def ep12925 : ℝ := (13003877522666491 / 25000000000000000000)
noncomputable def em12925 : ℝ := (50622079653252299 / 100000000000000000000)
noncomputable def bp12925 : ℝ := (43154840991990516363 / 100000000000000000000)
noncomputable def bm12925 : ℝ := (44137387464336707991 / 100000000000000000000)

theorem positive12925 :
    Eplus aL (agent12925.root+dsL) scalar12925.worldRadius world12925.frame
      agent12925.frame tp12925 ≤ -ep12925 := by
  apply positive_check (eT := (7228565924338428451 / 6250000000000000000)) (y := (9503697280342063457 / 25000000000000000000)) (u := (146250086446909973579 / 100000000000000000000))
  · norm_num [world12925, agent12925, scalar12925, tp12925, tm12925, ep12925, em12925, dsL]
  · norm_num [world12925, agent12925, scalar12925, tp12925, tm12925, ep12925, em12925, dsL]
  · norm_num [world12925, agent12925, scalar12925, tp12925, tm12925, ep12925, em12925, dsL]
  · norm_num [world12925, agent12925, scalar12925, tp12925, tm12925, ep12925, em12925, dsL]
  · norm_num [world12925, agent12925, scalar12925, tp12925, tm12925, ep12925, em12925, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12925, agent12925, tp12925, tm12925, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12925, agent12925, scalar12925, tp12925, tm12925, ep12925, em12925, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12925, agent12925, tp12925, tm12925, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12925, agent12925, scalar12925, tp12925, tm12925, ep12925, em12925, dsL]

theorem negative12925 :
    Eminus aL (agent12925.root+dsL) scalar12925.worldRadius world12925.frame
      agent12925.frame tm12925 ≤ -em12925 := by
  apply negative_check (lo := (68372385449156374277 / 100000000000000000000)) (hi := (34186192724578187139 / 50000000000000000000))
    (y := (-((14330400394966502177 / 20000000000000000000)))) (u := (48844909496886100997 / 100000000000000000000))
  · norm_num [world12925, agent12925, scalar12925, tp12925, tm12925, ep12925, em12925, dsL]
  · norm_num [world12925, agent12925, scalar12925, tp12925, tm12925, ep12925, em12925, dsL]
  · norm_num [world12925, agent12925, scalar12925, tp12925, tm12925, ep12925, em12925, dsL]
  · norm_num [world12925, agent12925, scalar12925, tp12925, tm12925, ep12925, em12925, dsL]
  · norm_num [world12925, agent12925, scalar12925, tp12925, tm12925, ep12925, em12925, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12925, agent12925, tp12925, tm12925, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12925, agent12925, tp12925, tm12925, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12925, agent12925, scalar12925, tp12925, tm12925, ep12925, em12925, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12925, agent12925, tp12925, tm12925, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12925, agent12925, scalar12925, tp12925, tm12925, ep12925, em12925, dsL]

theorem tails12925 :
    exp (-((12925:ℝ)*ep12925)) ≤ scalar12925.upperTail ∧
    exp (-((12925:ℝ)*em12925)) ≤ scalar12925.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12925:ℝ)) (by norm_num [ep12925]) ?_)
      (show bp12925^8 ≤ scalar12925.upperTail by norm_num [bp12925, scalar12925])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12925, bp12925, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12925:ℝ)) (by norm_num [em12925]) ?_)
      (show bm12925^8 ≤ scalar12925.lowerTail by norm_num [bm12925, scalar12925])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12925, bm12925, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12925 :
    agent12925.root+dsL+scalar12925.worldRadius < √(1/100/aL) ∧
    2*(agent12925.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12925, agent12925, scalar12925, tp12925, tm12925, ep12925, em12925, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12925, agent12925, scalar12925, tp12925, tm12925, ep12925, em12925, dsL]

noncomputable def master12925 : MasterCertificate 12925 world12925 agent12925 :=
  master scalar12925 dsL tp12925 tm12925 ep12925 em12925
    (by norm_num [dsL]) (by norm_num [tp12925]) (by norm_num [tm12925])
    (by norm_num [ep12925]) (by norm_num [em12925])
    positive12925 negative12925 tails12925.1 tails12925.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12925.1 tailGuards12925.2

theorem preserves12925 : master12925.toScalarCertificate = scalar12925 := rfl

noncomputable def tp12926 : ℝ := (584130013 / 2500000000)
noncomputable def tm12926 : ℝ := (-((6107156891 / 10000000000)))
noncomputable def ep12926 : ℝ := (52017873083157193 / 100000000000000000000)
noncomputable def em12926 : ℝ := (50624093792587963 / 100000000000000000000)
noncomputable def bp12926 : ℝ := (2696899229150834877 / 6250000000000000000)
noncomputable def bm12926 : ℝ := (5516644796985884239 / 12500000000000000000)

theorem positive12926 :
    Eplus aL (agent12926.root+dsL) scalar12926.worldRadius world12926.frame
      agent12926.frame tp12926 ≤ -ep12926 := by
  apply positive_check (eT := (23131451122645768511 / 20000000000000000000)) (y := (38015499345067539919 / 100000000000000000000)) (u := (29250225030674542259 / 20000000000000000000))
  · norm_num [world12926, agent12926, scalar12926, tp12926, tm12926, ep12926, em12926, dsL]
  · norm_num [world12926, agent12926, scalar12926, tp12926, tm12926, ep12926, em12926, dsL]
  · norm_num [world12926, agent12926, scalar12926, tp12926, tm12926, ep12926, em12926, dsL]
  · norm_num [world12926, agent12926, scalar12926, tp12926, tm12926, ep12926, em12926, dsL]
  · norm_num [world12926, agent12926, scalar12926, tp12926, tm12926, ep12926, em12926, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12926, agent12926, tp12926, tm12926, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12926, agent12926, scalar12926, tp12926, tm12926, ep12926, em12926, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12926, agent12926, tp12926, tm12926, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12926, agent12926, scalar12926, tp12926, tm12926, ep12926, em12926, dsL]

theorem negative12926 :
    Eminus aL (agent12926.root+dsL) scalar12926.worldRadius world12926.frame
      agent12926.frame tm12926 ≤ -em12926 := by
  apply negative_check (lo := (68372235391616870629 / 100000000000000000000)) (hi := (6837223539161687063 / 10000000000000000000))
    (y := (-((35825989028692508119 / 50000000000000000000)))) (u := (12211230294835770199 / 25000000000000000000))
  · norm_num [world12926, agent12926, scalar12926, tp12926, tm12926, ep12926, em12926, dsL]
  · norm_num [world12926, agent12926, scalar12926, tp12926, tm12926, ep12926, em12926, dsL]
  · norm_num [world12926, agent12926, scalar12926, tp12926, tm12926, ep12926, em12926, dsL]
  · norm_num [world12926, agent12926, scalar12926, tp12926, tm12926, ep12926, em12926, dsL]
  · norm_num [world12926, agent12926, scalar12926, tp12926, tm12926, ep12926, em12926, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12926, agent12926, tp12926, tm12926, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12926, agent12926, tp12926, tm12926, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12926, agent12926, scalar12926, tp12926, tm12926, ep12926, em12926, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12926, agent12926, tp12926, tm12926, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12926, agent12926, scalar12926, tp12926, tm12926, ep12926, em12926, dsL]

theorem tails12926 :
    exp (-((12926:ℝ)*ep12926)) ≤ scalar12926.upperTail ∧
    exp (-((12926:ℝ)*em12926)) ≤ scalar12926.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12926:ℝ)) (by norm_num [ep12926]) ?_)
      (show bp12926^8 ≤ scalar12926.upperTail by norm_num [bp12926, scalar12926])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12926, bp12926, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12926:ℝ)) (by norm_num [em12926]) ?_)
      (show bm12926^8 ≤ scalar12926.lowerTail by norm_num [bm12926, scalar12926])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12926, bm12926, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12926 :
    agent12926.root+dsL+scalar12926.worldRadius < √(1/100/aL) ∧
    2*(agent12926.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12926, agent12926, scalar12926, tp12926, tm12926, ep12926, em12926, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12926, agent12926, scalar12926, tp12926, tm12926, ep12926, em12926, dsL]

noncomputable def master12926 : MasterCertificate 12926 world12926 agent12926 :=
  master scalar12926 dsL tp12926 tm12926 ep12926 em12926
    (by norm_num [dsL]) (by norm_num [tp12926]) (by norm_num [tm12926])
    (by norm_num [ep12926]) (by norm_num [em12926])
    positive12926 negative12926 tails12926.1 tails12926.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12926.1 tailGuards12926.2

theorem preserves12926 : master12926.toScalarCertificate = scalar12926 := rfl

noncomputable def tp12927 : ℝ := (1168299013 / 5000000000)
noncomputable def tm12927 : ℝ := (-((1221464619 / 2000000000)))
noncomputable def ep12927 : ℝ := (26010117567781787 / 50000000000000000000)
noncomputable def em12927 : ℝ := (50626107091402481 / 100000000000000000000)
noncomputable def bp12927 : ℝ := (43145935200921854771 / 100000000000000000000)
noncomputable def bm12927 : ℝ := (44128930069798235393 / 100000000000000000000)

theorem positive12927 :
    Eplus aL (agent12927.root+dsL) scalar12927.worldRadius world12927.frame
      agent12927.frame tp12927 ≤ -ep12927 := by
  apply positive_check (eT := (115657456153151458403 / 100000000000000000000)) (y := (38016209032420048459 / 100000000000000000000)) (u := (5850086523311753951 / 4000000000000000000))
  · norm_num [world12927, agent12927, scalar12927, tp12927, tm12927, ep12927, em12927, dsL]
  · norm_num [world12927, agent12927, scalar12927, tp12927, tm12927, ep12927, em12927, dsL]
  · norm_num [world12927, agent12927, scalar12927, tp12927, tm12927, ep12927, em12927, dsL]
  · norm_num [world12927, agent12927, scalar12927, tp12927, tm12927, ep12927, em12927, dsL]
  · norm_num [world12927, agent12927, scalar12927, tp12927, tm12927, ep12927, em12927, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12927, agent12927, tp12927, tm12927, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12927, agent12927, scalar12927, tp12927, tm12927, ep12927, em12927, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12927, agent12927, tp12927, tm12927, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12927, agent12927, scalar12927, tp12927, tm12927, ep12927, em12927, dsL]

theorem negative12927 :
    Eminus aL (agent12927.root+dsL) scalar12927.worldRadius world12927.frame
      agent12927.frame tm12927 ≤ -em12927 := by
  apply negative_check (lo := (17093021394854545629 / 25000000000000000000)) (hi := (68372085579418182517 / 100000000000000000000))
    (y := (-((17912988518852993489 / 25000000000000000000)))) (u := (48844932893320315171 / 100000000000000000000))
  · norm_num [world12927, agent12927, scalar12927, tp12927, tm12927, ep12927, em12927, dsL]
  · norm_num [world12927, agent12927, scalar12927, tp12927, tm12927, ep12927, em12927, dsL]
  · norm_num [world12927, agent12927, scalar12927, tp12927, tm12927, ep12927, em12927, dsL]
  · norm_num [world12927, agent12927, scalar12927, tp12927, tm12927, ep12927, em12927, dsL]
  · norm_num [world12927, agent12927, scalar12927, tp12927, tm12927, ep12927, em12927, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12927, agent12927, tp12927, tm12927, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12927, agent12927, tp12927, tm12927, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12927, agent12927, scalar12927, tp12927, tm12927, ep12927, em12927, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12927, agent12927, tp12927, tm12927, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12927, agent12927, scalar12927, tp12927, tm12927, ep12927, em12927, dsL]

theorem tails12927 :
    exp (-((12927:ℝ)*ep12927)) ≤ scalar12927.upperTail ∧
    exp (-((12927:ℝ)*em12927)) ≤ scalar12927.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12927:ℝ)) (by norm_num [ep12927]) ?_)
      (show bp12927^8 ≤ scalar12927.upperTail by norm_num [bp12927, scalar12927])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12927, bp12927, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12927:ℝ)) (by norm_num [em12927]) ?_)
      (show bm12927^8 ≤ scalar12927.lowerTail by norm_num [bm12927, scalar12927])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12927, bm12927, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12927 :
    agent12927.root+dsL+scalar12927.worldRadius < √(1/100/aL) ∧
    2*(agent12927.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12927, agent12927, scalar12927, tp12927, tm12927, ep12927, em12927, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12927, agent12927, scalar12927, tp12927, tm12927, ep12927, em12927, dsL]

noncomputable def master12927 : MasterCertificate 12927 world12927 agent12927 :=
  master scalar12927 dsL tp12927 tm12927 ep12927 em12927
    (by norm_num [dsL]) (by norm_num [tp12927]) (by norm_num [tm12927])
    (by norm_num [ep12927]) (by norm_num [em12927])
    positive12927 negative12927 tails12927.1 tails12927.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12927.1 tailGuards12927.2

theorem preserves12927 : master12927.toScalarCertificate = scalar12927 := rfl

noncomputable def tp12928 : ℝ := (18255281 / 78125000)
noncomputable def tm12928 : ℝ := (-((1526872327 / 2500000000)))
noncomputable def ep12928 : ℝ := (52022595431680193 / 100000000000000000000)
noncomputable def em12928 : ℝ := (50628118748353759 / 100000000000000000000)
noncomputable def bp12928 : ℝ := (8628296832905461967 / 20000000000000000000)
noncomputable def bm12928 : ℝ := (1378896972420724691 / 3125000000000000000)

theorem positive12928 :
    Eplus aL (agent12928.root+dsL) scalar12928.worldRadius world12928.frame
      agent12928.frame tp12928 ≤ -ep12928 := by
  apply positive_check (eT := (115657656495634338057 / 100000000000000000000)) (y := (38016918542616675219 / 100000000000000000000)) (u := (36563300190121229639 / 25000000000000000000))
  · norm_num [world12928, agent12928, scalar12928, tp12928, tm12928, ep12928, em12928, dsL]
  · norm_num [world12928, agent12928, scalar12928, tp12928, tm12928, ep12928, em12928, dsL]
  · norm_num [world12928, agent12928, scalar12928, tp12928, tm12928, ep12928, em12928, dsL]
  · norm_num [world12928, agent12928, scalar12928, tp12928, tm12928, ep12928, em12928, dsL]
  · norm_num [world12928, agent12928, scalar12928, tp12928, tm12928, ep12928, em12928, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12928, agent12928, tp12928, tm12928, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12928, agent12928, scalar12928, tp12928, tm12928, ep12928, em12928, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12928, agent12928, tp12928, tm12928, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12928, agent12928, scalar12928, tp12928, tm12928, ep12928, em12928, dsL]

theorem negative12928 :
    Eminus aL (agent12928.root+dsL) scalar12928.worldRadius world12928.frame
      agent12928.frame tm12928 ≤ -em12928 := by
  apply negative_check (lo := (68371935671983295933 / 100000000000000000000)) (hi := (34185967835991647967 / 50000000000000000000))
    (y := (-((17912982605659577363 / 25000000000000000000)))) (u := (48844944446503105331 / 100000000000000000000))
  · norm_num [world12928, agent12928, scalar12928, tp12928, tm12928, ep12928, em12928, dsL]
  · norm_num [world12928, agent12928, scalar12928, tp12928, tm12928, ep12928, em12928, dsL]
  · norm_num [world12928, agent12928, scalar12928, tp12928, tm12928, ep12928, em12928, dsL]
  · norm_num [world12928, agent12928, scalar12928, tp12928, tm12928, ep12928, em12928, dsL]
  · norm_num [world12928, agent12928, scalar12928, tp12928, tm12928, ep12928, em12928, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12928, agent12928, tp12928, tm12928, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12928, agent12928, tp12928, tm12928, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12928, agent12928, scalar12928, tp12928, tm12928, ep12928, em12928, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12928, agent12928, tp12928, tm12928, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12928, agent12928, scalar12928, tp12928, tm12928, ep12928, em12928, dsL]

theorem tails12928 :
    exp (-((12928:ℝ)*ep12928)) ≤ scalar12928.upperTail ∧
    exp (-((12928:ℝ)*em12928)) ≤ scalar12928.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12928:ℝ)) (by norm_num [ep12928]) ?_)
      (show bp12928^8 ≤ scalar12928.upperTail by norm_num [bp12928, scalar12928])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12928, bp12928, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12928:ℝ)) (by norm_num [em12928]) ?_)
      (show bm12928^8 ≤ scalar12928.lowerTail by norm_num [bm12928, scalar12928])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12928, bm12928, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12928 :
    agent12928.root+dsL+scalar12928.worldRadius < √(1/100/aL) ∧
    2*(agent12928.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12928, agent12928, scalar12928, tp12928, tm12928, ep12928, em12928, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12928, agent12928, scalar12928, tp12928, tm12928, ep12928, em12928, dsL]

noncomputable def master12928 : MasterCertificate 12928 world12928 agent12928 :=
  master scalar12928 dsL tp12928 tm12928 ep12928 em12928
    (by norm_num [dsL]) (by norm_num [tp12928]) (by norm_num [tm12928])
    (by norm_num [ep12928]) (by norm_num [em12928])
    positive12928 negative12928 tails12928.1 tails12928.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12928.1 tailGuards12928.2

theorem preserves12928 : master12928.toScalarCertificate = scalar12928 := rfl

noncomputable def tp12929 : ℝ := (584188457 / 2500000000)
noncomputable def tm12929 : ℝ := (-((1221531061 / 2000000000)))
noncomputable def ep12929 : ℝ := (26012477250494077 / 50000000000000000000)
noncomputable def em12929 : ℝ := (50630129265538179 / 100000000000000000000)
noncomputable def bp12929 : ℝ := (43137034188039418471 / 100000000000000000000)
noncomputable def bm12929 : ℝ := (22060238580413165639 / 50000000000000000000)

theorem positive12929 :
    Eplus aL (agent12929.root+dsL) scalar12929.worldRadius world12929.frame
      agent12929.frame tp12929 ≤ -ep12929 := by
  apply positive_check (eT := (11565785628064988799 / 10000000000000000000)) (y := (9504406789066468507 / 25000000000000000000)) (u := (73127118567149918153 / 50000000000000000000))
  · norm_num [world12929, agent12929, scalar12929, tp12929, tm12929, ep12929, em12929, dsL]
  · norm_num [world12929, agent12929, scalar12929, tp12929, tm12929, ep12929, em12929, dsL]
  · norm_num [world12929, agent12929, scalar12929, tp12929, tm12929, ep12929, em12929, dsL]
  · norm_num [world12929, agent12929, scalar12929, tp12929, tm12929, ep12929, em12929, dsL]
  · norm_num [world12929, agent12929, scalar12929, tp12929, tm12929, ep12929, em12929, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12929, agent12929, tp12929, tm12929, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12929, agent12929, scalar12929, tp12929, tm12929, ep12929, em12929, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12929, agent12929, tp12929, tm12929, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12929, agent12929, scalar12929, tp12929, tm12929, ep12929, em12929, dsL]

theorem negative12929 :
    Eminus aL (agent12929.root+dsL) scalar12929.worldRadius world12929.frame
      agent12929.frame tm12929 ≤ -em12929 := by
  apply negative_check (lo := (2136618332095159559 / 3125000000000000000)) (hi := (68371786627045105889 / 100000000000000000000))
    (y := (-((17912976470063036399 / 25000000000000000000)))) (u := (12211239108554865987 / 25000000000000000000))
  · norm_num [world12929, agent12929, scalar12929, tp12929, tm12929, ep12929, em12929, dsL]
  · norm_num [world12929, agent12929, scalar12929, tp12929, tm12929, ep12929, em12929, dsL]
  · norm_num [world12929, agent12929, scalar12929, tp12929, tm12929, ep12929, em12929, dsL]
  · norm_num [world12929, agent12929, scalar12929, tp12929, tm12929, ep12929, em12929, dsL]
  · norm_num [world12929, agent12929, scalar12929, tp12929, tm12929, ep12929, em12929, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12929, agent12929, tp12929, tm12929, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12929, agent12929, tp12929, tm12929, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12929, agent12929, scalar12929, tp12929, tm12929, ep12929, em12929, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12929, agent12929, tp12929, tm12929, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12929, agent12929, scalar12929, tp12929, tm12929, ep12929, em12929, dsL]

theorem tails12929 :
    exp (-((12929:ℝ)*ep12929)) ≤ scalar12929.upperTail ∧
    exp (-((12929:ℝ)*em12929)) ≤ scalar12929.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12929:ℝ)) (by norm_num [ep12929]) ?_)
      (show bp12929^8 ≤ scalar12929.upperTail by norm_num [bp12929, scalar12929])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12929, bp12929, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12929:ℝ)) (by norm_num [em12929]) ?_)
      (show bm12929^8 ≤ scalar12929.lowerTail by norm_num [bm12929, scalar12929])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12929, bm12929, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12929 :
    agent12929.root+dsL+scalar12929.worldRadius < √(1/100/aL) ∧
    2*(agent12929.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12929, agent12929, scalar12929, tp12929, tm12929, ep12929, em12929, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12929, agent12929, scalar12929, tp12929, tm12929, ep12929, em12929, dsL]

noncomputable def master12929 : MasterCertificate 12929 world12929 agent12929 :=
  master scalar12929 dsL tp12929 tm12929 ep12929 em12929
    (by norm_num [dsL]) (by norm_num [tp12929]) (by norm_num [tm12929])
    (by norm_num [ep12929]) (by norm_num [em12929])
    positive12929 negative12929 tails12929.1 tails12929.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12929.1 tailGuards12929.2

theorem preserves12929 : master12929.toScalarCertificate = scalar12929 := rfl

noncomputable def tp12930 : ℝ := (1168452051 / 5000000000)
noncomputable def tm12930 : ℝ := (-((6108040463 / 10000000000)))
noncomputable def ep12930 : ℝ := (52028686296608403 / 100000000000000000000)
noncomputable def em12930 : ℝ := (1265840938165653 / 2500000000000000000)
noncomputable def bp12930 : ℝ := (43131627457556476417 / 100000000000000000000)
noncomputable def bm12930 : ℝ := (22057591732699599853 / 50000000000000000000)

theorem positive12930 :
    Eplus aL (agent12930.root+dsL) scalar12930.worldRadius world12930.frame
      agent12930.frame tp12930 ≤ -ep12930 := by
  apply positive_check (eT := (1156585774601916543 / 1000000000000000000)) (y := (19008808971151893877 / 50000000000000000000)) (u := (146254223658490498011 / 100000000000000000000))
  · norm_num [world12930, agent12930, scalar12930, tp12930, tm12930, ep12930, em12930, dsL]
  · norm_num [world12930, agent12930, scalar12930, tp12930, tm12930, ep12930, em12930, dsL]
  · norm_num [world12930, agent12930, scalar12930, tp12930, tm12930, ep12930, em12930, dsL]
  · norm_num [world12930, agent12930, scalar12930, tp12930, tm12930, ep12930, em12930, dsL]
  · norm_num [world12930, agent12930, scalar12930, tp12930, tm12930, ep12930, em12930, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12930, agent12930, tp12930, tm12930, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12930, agent12930, scalar12930, tp12930, tm12930, ep12930, em12930, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12930, agent12930, tp12930, tm12930, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12930, agent12930, scalar12930, tp12930, tm12930, ep12930, em12930, dsL]

theorem negative12930 :
    Eminus aL (agent12930.root+dsL) scalar12930.worldRadius world12930.frame
      agent12930.frame tm12930 ≤ -em12930 := by
  apply negative_check (lo := (13674140950466399283 / 20000000000000000000)) (hi := (267073065438796861 / 390625000000000000))
    (y := (-((573200007495502679 / 800000000000000000)))) (u := (24422943455906971411 / 50000000000000000000))
  · norm_num [world12930, agent12930, scalar12930, tp12930, tm12930, ep12930, em12930, dsL]
  · norm_num [world12930, agent12930, scalar12930, tp12930, tm12930, ep12930, em12930, dsL]
  · norm_num [world12930, agent12930, scalar12930, tp12930, tm12930, ep12930, em12930, dsL]
  · norm_num [world12930, agent12930, scalar12930, tp12930, tm12930, ep12930, em12930, dsL]
  · norm_num [world12930, agent12930, scalar12930, tp12930, tm12930, ep12930, em12930, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12930, agent12930, tp12930, tm12930, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12930, agent12930, tp12930, tm12930, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12930, agent12930, scalar12930, tp12930, tm12930, ep12930, em12930, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12930, agent12930, tp12930, tm12930, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12930, agent12930, scalar12930, tp12930, tm12930, ep12930, em12930, dsL]

theorem tails12930 :
    exp (-((12930:ℝ)*ep12930)) ≤ scalar12930.upperTail ∧
    exp (-((12930:ℝ)*em12930)) ≤ scalar12930.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12930:ℝ)) (by norm_num [ep12930]) ?_)
      (show bp12930^8 ≤ scalar12930.upperTail by norm_num [bp12930, scalar12930])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12930, bp12930, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12930:ℝ)) (by norm_num [em12930]) ?_)
      (show bm12930^8 ≤ scalar12930.lowerTail by norm_num [bm12930, scalar12930])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12930, bm12930, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12930 :
    agent12930.root+dsL+scalar12930.worldRadius < √(1/100/aL) ∧
    2*(agent12930.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12930, agent12930, scalar12930, tp12930, tm12930, ep12930, em12930, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12930, agent12930, scalar12930, tp12930, tm12930, ep12930, em12930, dsL]

noncomputable def master12930 : MasterCertificate 12930 world12930 agent12930 :=
  master scalar12930 dsL tp12930 tm12930 ep12930 em12930
    (by norm_num [dsL]) (by norm_num [tp12930]) (by norm_num [tm12930])
    (by norm_num [ep12930]) (by norm_num [em12930])
    positive12930 negative12930 tails12930.1 tails12930.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12930.1 tailGuards12930.2

theorem preserves12930 : master12930.toScalarCertificate = scalar12930 := rfl

noncomputable def tp12931 : ℝ := (2336981937 / 10000000000)
noncomputable def tm12931 : ℝ := (-((6108206353 / 10000000000)))
noncomputable def ep12931 : ℝ := (52031043236663861 / 100000000000000000000)
noncomputable def em12931 : ℝ := (50635646089534107 / 100000000000000000000)
noncomputable def bp12931 : ℝ := (43127179399365577407 / 100000000000000000000)
noncomputable def bm12931 : ℝ := (22055479643935811667 / 50000000000000000000)

theorem positive12931 :
    Eplus aL (agent12931.root+dsL) scalar12931.worldRadius world12931.frame
      agent12931.frame tp12931 ≤ -ep12931 := by
  apply positive_check (eT := (115658777120846643609 / 100000000000000000000)) (y := (19009163305712230587 / 50000000000000000000)) (u := (14625526012068378579 / 10000000000000000000))
  · norm_num [world12931, agent12931, scalar12931, tp12931, tm12931, ep12931, em12931, dsL]
  · norm_num [world12931, agent12931, scalar12931, tp12931, tm12931, ep12931, em12931, dsL]
  · norm_num [world12931, agent12931, scalar12931, tp12931, tm12931, ep12931, em12931, dsL]
  · norm_num [world12931, agent12931, scalar12931, tp12931, tm12931, ep12931, em12931, dsL]
  · norm_num [world12931, agent12931, scalar12931, tp12931, tm12931, ep12931, em12931, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12931, agent12931, tp12931, tm12931, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12931, agent12931, scalar12931, tp12931, tm12931, ep12931, em12931, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12931, agent12931, tp12931, tm12931, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12931, agent12931, scalar12931, tp12931, tm12931, ep12931, em12931, dsL]

theorem negative12931 :
    Eminus aL (agent12931.root+dsL) scalar12931.worldRadius world12931.frame
      agent12931.frame tm12931 ≤ -em12931 := by
  apply negative_check (lo := (68370556071007897757 / 100000000000000000000)) (hi := (34185278035503948879 / 50000000000000000000))
    (y := (-((35824988129344331927 / 50000000000000000000)))) (u := (48845898966125112111 / 100000000000000000000))
  · norm_num [world12931, agent12931, scalar12931, tp12931, tm12931, ep12931, em12931, dsL]
  · norm_num [world12931, agent12931, scalar12931, tp12931, tm12931, ep12931, em12931, dsL]
  · norm_num [world12931, agent12931, scalar12931, tp12931, tm12931, ep12931, em12931, dsL]
  · norm_num [world12931, agent12931, scalar12931, tp12931, tm12931, ep12931, em12931, dsL]
  · norm_num [world12931, agent12931, scalar12931, tp12931, tm12931, ep12931, em12931, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12931, agent12931, tp12931, tm12931, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12931, agent12931, tp12931, tm12931, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12931, agent12931, scalar12931, tp12931, tm12931, ep12931, em12931, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12931, agent12931, tp12931, tm12931, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12931, agent12931, scalar12931, tp12931, tm12931, ep12931, em12931, dsL]

theorem tails12931 :
    exp (-((12931:ℝ)*ep12931)) ≤ scalar12931.upperTail ∧
    exp (-((12931:ℝ)*em12931)) ≤ scalar12931.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12931:ℝ)) (by norm_num [ep12931]) ?_)
      (show bp12931^8 ≤ scalar12931.upperTail by norm_num [bp12931, scalar12931])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12931, bp12931, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12931:ℝ)) (by norm_num [em12931]) ?_)
      (show bm12931^8 ≤ scalar12931.lowerTail by norm_num [bm12931, scalar12931])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12931, bm12931, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12931 :
    agent12931.root+dsL+scalar12931.worldRadius < √(1/100/aL) ∧
    2*(agent12931.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12931, agent12931, scalar12931, tp12931, tm12931, ep12931, em12931, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12931, agent12931, scalar12931, tp12931, tm12931, ep12931, em12931, dsL]

noncomputable def master12931 : MasterCertificate 12931 world12931 agent12931 :=
  master scalar12931 dsL tp12931 tm12931 ep12931 em12931
    (by norm_num [dsL]) (by norm_num [tp12931]) (by norm_num [tm12931])
    (by norm_num [ep12931]) (by norm_num [em12931])
    positive12931 negative12931 tails12931.1 tails12931.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12931.1 tailGuards12931.2

theorem preserves12931 : master12931.toScalarCertificate = scalar12931 := rfl

noncomputable def tp12932 : ℝ := (2337059667 / 10000000000)
noncomputable def tm12932 : ℝ := (-((1221674433 / 2000000000)))
noncomputable def ep12932 : ℝ := (2081335969339671 / 4000000000000000000)
noncomputable def em12932 : ℝ := (25318826873248851 / 50000000000000000000)
noncomputable def bp12932 : ℝ := (43122732203301773683 / 100000000000000000000)
noncomputable def bm12932 : ℝ := (22053367969635255341 / 50000000000000000000)

theorem positive12932 :
    Eplus aL (agent12932.root+dsL) scalar12932.worldRadius world12932.frame
      agent12932.frame tp12932 ≤ -ep12932 := by
  apply positive_check (eT := (115658976058474498323 / 100000000000000000000)) (y := (9504758470165065021 / 25000000000000000000)) (u := (146256294542802427453 / 100000000000000000000))
  · norm_num [world12932, agent12932, scalar12932, tp12932, tm12932, ep12932, em12932, dsL]
  · norm_num [world12932, agent12932, scalar12932, tp12932, tm12932, ep12932, em12932, dsL]
  · norm_num [world12932, agent12932, scalar12932, tp12932, tm12932, ep12932, em12932, dsL]
  · norm_num [world12932, agent12932, scalar12932, tp12932, tm12932, ep12932, em12932, dsL]
  · norm_num [world12932, agent12932, scalar12932, tp12932, tm12932, ep12932, em12932, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12932, agent12932, tp12932, tm12932, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12932, agent12932, scalar12932, tp12932, tm12932, ep12932, em12932, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12932, agent12932, tp12932, tm12932, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12932, agent12932, scalar12932, tp12932, tm12932, ep12932, em12932, dsL]

theorem negative12932 :
    Eminus aL (agent12932.root+dsL) scalar12932.worldRadius world12932.frame
      agent12932.frame tm12932 ≤ -em12932 := by
  apply negative_check (lo := (34185203832393748917 / 50000000000000000000)) (hi := (13674081532957499567 / 20000000000000000000))
    (y := (-((71649951612560284657 / 100000000000000000000)))) (u := (48845911004749562803 / 100000000000000000000))
  · norm_num [world12932, agent12932, scalar12932, tp12932, tm12932, ep12932, em12932, dsL]
  · norm_num [world12932, agent12932, scalar12932, tp12932, tm12932, ep12932, em12932, dsL]
  · norm_num [world12932, agent12932, scalar12932, tp12932, tm12932, ep12932, em12932, dsL]
  · norm_num [world12932, agent12932, scalar12932, tp12932, tm12932, ep12932, em12932, dsL]
  · norm_num [world12932, agent12932, scalar12932, tp12932, tm12932, ep12932, em12932, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12932, agent12932, tp12932, tm12932, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12932, agent12932, tp12932, tm12932, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12932, agent12932, scalar12932, tp12932, tm12932, ep12932, em12932, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12932, agent12932, tp12932, tm12932, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12932, agent12932, scalar12932, tp12932, tm12932, ep12932, em12932, dsL]

theorem tails12932 :
    exp (-((12932:ℝ)*ep12932)) ≤ scalar12932.upperTail ∧
    exp (-((12932:ℝ)*em12932)) ≤ scalar12932.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12932:ℝ)) (by norm_num [ep12932]) ?_)
      (show bp12932^8 ≤ scalar12932.upperTail by norm_num [bp12932, scalar12932])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12932, bp12932, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12932:ℝ)) (by norm_num [em12932]) ?_)
      (show bm12932^8 ≤ scalar12932.lowerTail by norm_num [bm12932, scalar12932])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12932, bm12932, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12932 :
    agent12932.root+dsL+scalar12932.worldRadius < √(1/100/aL) ∧
    2*(agent12932.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12932, agent12932, scalar12932, tp12932, tm12932, ep12932, em12932, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12932, agent12932, scalar12932, tp12932, tm12932, ep12932, em12932, dsL]

noncomputable def master12932 : MasterCertificate 12932 world12932 agent12932 :=
  master scalar12932 dsL tp12932 tm12932 ep12932 em12932
    (by norm_num [dsL]) (by norm_num [tp12932]) (by norm_num [tm12932])
    (by norm_num [ep12932]) (by norm_num [em12932])
    positive12932 negative12932 tails12932.1 tails12932.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12932.1 tailGuards12932.2

theorem preserves12932 : master12932.toScalarCertificate = scalar12932 := rfl

noncomputable def tp12933 : ℝ := (2337137441 / 10000000000)
noncomputable def tm12933 : ℝ := (-((122170757 / 200000000)))
noncomputable def ep12933 : ℝ := (416286024199411 / 800000000000000000)
noncomputable def em12933 : ℝ := (25319829675809191 / 50000000000000000000)
noncomputable def bp12933 : ℝ := (862365734983040097 / 2000000000000000000)
noncomputable def bm12933 : ℝ := (2756407139786181909 / 6250000000000000000)

theorem positive12933 :
    Eplus aL (agent12933.root+dsL) scalar12933.worldRadius world12933.frame
      agent12933.frame tp12933 ≤ -ep12933 := by
  apply positive_check (eT := (115659175345852195621 / 100000000000000000000)) (y := (38019742451887550969 / 100000000000000000000)) (u := (146257330876495236407 / 100000000000000000000))
  · norm_num [world12933, agent12933, scalar12933, tp12933, tm12933, ep12933, em12933, dsL]
  · norm_num [world12933, agent12933, scalar12933, tp12933, tm12933, ep12933, em12933, dsL]
  · norm_num [world12933, agent12933, scalar12933, tp12933, tm12933, ep12933, em12933, dsL]
  · norm_num [world12933, agent12933, scalar12933, tp12933, tm12933, ep12933, em12933, dsL]
  · norm_num [world12933, agent12933, scalar12933, tp12933, tm12933, ep12933, em12933, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12933, agent12933, tp12933, tm12933, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12933, agent12933, scalar12933, tp12933, tm12933, ep12933, em12933, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12933, agent12933, tp12933, tm12933, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12933, agent12933, scalar12933, tp12933, tm12933, ep12933, em12933, dsL]

theorem negative12933 :
    Eminus aL (agent12933.root+dsL) scalar12933.worldRadius world12933.frame
      agent12933.frame tm12933 ≤ -em12933 := by
  apply negative_check (lo := (2734810389685274809 / 4000000000000000000)) (hi := (34185129871065935113 / 50000000000000000000))
    (y := (-((71649926266815560541 / 100000000000000000000)))) (u := (48845923385111043183 / 100000000000000000000))
  · norm_num [world12933, agent12933, scalar12933, tp12933, tm12933, ep12933, em12933, dsL]
  · norm_num [world12933, agent12933, scalar12933, tp12933, tm12933, ep12933, em12933, dsL]
  · norm_num [world12933, agent12933, scalar12933, tp12933, tm12933, ep12933, em12933, dsL]
  · norm_num [world12933, agent12933, scalar12933, tp12933, tm12933, ep12933, em12933, dsL]
  · norm_num [world12933, agent12933, scalar12933, tp12933, tm12933, ep12933, em12933, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12933, agent12933, tp12933, tm12933, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12933, agent12933, tp12933, tm12933, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12933, agent12933, scalar12933, tp12933, tm12933, ep12933, em12933, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12933, agent12933, tp12933, tm12933, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12933, agent12933, scalar12933, tp12933, tm12933, ep12933, em12933, dsL]

theorem tails12933 :
    exp (-((12933:ℝ)*ep12933)) ≤ scalar12933.upperTail ∧
    exp (-((12933:ℝ)*em12933)) ≤ scalar12933.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12933:ℝ)) (by norm_num [ep12933]) ?_)
      (show bp12933^8 ≤ scalar12933.upperTail by norm_num [bp12933, scalar12933])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12933, bp12933, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12933:ℝ)) (by norm_num [em12933]) ?_)
      (show bm12933^8 ≤ scalar12933.lowerTail by norm_num [bm12933, scalar12933])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12933, bm12933, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12933 :
    agent12933.root+dsL+scalar12933.worldRadius < √(1/100/aL) ∧
    2*(agent12933.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12933, agent12933, scalar12933, tp12933, tm12933, ep12933, em12933, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12933, agent12933, scalar12933, tp12933, tm12933, ep12933, em12933, dsL]

noncomputable def master12933 : MasterCertificate 12933 world12933 agent12933 :=
  master scalar12933 dsL tp12933 tm12933 ep12933 em12933
    (by norm_num [dsL]) (by norm_num [tp12933]) (by norm_num [tm12933])
    (by norm_num [ep12933]) (by norm_num [em12933])
    positive12933 negative12933 tails12933.1 tails12933.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12933.1 tailGuards12933.2

theorem preserves12933 : master12933.toScalarCertificate = scalar12933 := rfl

noncomputable def tp12934 : ℝ := (1168607583 / 5000000000)
noncomputable def tm12934 : ℝ := (-((3054351643 / 5000000000)))
noncomputable def ep12934 : ℝ := (26019053180879957 / 50000000000000000000)
noncomputable def em12934 : ℝ := (25320832282709981 / 50000000000000000000)
noncomputable def bp12934 : ℝ := (21556920908225543737 / 50000000000000000000)
noncomputable def bm12934 : ℝ := (44098292995855244327 / 100000000000000000000)

theorem positive12934 :
    Eplus aL (agent12934.root+dsL) scalar12934.worldRadius world12934.frame
      agent12934.frame tp12934 ≤ -ep12934 := by
  apply positive_check (eT := (28914843578353941921 / 25000000000000000000)) (y := (38020450349362474273 / 100000000000000000000)) (u := (146258366232112025149 / 100000000000000000000))
  · norm_num [world12934, agent12934, scalar12934, tp12934, tm12934, ep12934, em12934, dsL]
  · norm_num [world12934, agent12934, scalar12934, tp12934, tm12934, ep12934, em12934, dsL]
  · norm_num [world12934, agent12934, scalar12934, tp12934, tm12934, ep12934, em12934, dsL]
  · norm_num [world12934, agent12934, scalar12934, tp12934, tm12934, ep12934, em12934, dsL]
  · norm_num [world12934, agent12934, scalar12934, tp12934, tm12934, ep12934, em12934, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12934, agent12934, tp12934, tm12934, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12934, agent12934, scalar12934, tp12934, tm12934, ep12934, em12934, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12934, agent12934, tp12934, tm12934, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12934, agent12934, scalar12934, tp12934, tm12934, ep12934, em12934, dsL]

theorem negative12934 :
    Eminus aL (agent12934.root+dsL) scalar12934.worldRadius world12934.frame
      agent12934.frame tm12934 ≤ -em12934 := by
  apply negative_check (lo := (68370112822230381601 / 100000000000000000000)) (hi := (34185056411115190801 / 50000000000000000000))
    (y := (-((71649899266906484339 / 100000000000000000000)))) (u := (6105742071683465627 / 12500000000000000000))
  · norm_num [world12934, agent12934, scalar12934, tp12934, tm12934, ep12934, em12934, dsL]
  · norm_num [world12934, agent12934, scalar12934, tp12934, tm12934, ep12934, em12934, dsL]
  · norm_num [world12934, agent12934, scalar12934, tp12934, tm12934, ep12934, em12934, dsL]
  · norm_num [world12934, agent12934, scalar12934, tp12934, tm12934, ep12934, em12934, dsL]
  · norm_num [world12934, agent12934, scalar12934, tp12934, tm12934, ep12934, em12934, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12934, agent12934, tp12934, tm12934, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12934, agent12934, tp12934, tm12934, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12934, agent12934, scalar12934, tp12934, tm12934, ep12934, em12934, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12934, agent12934, tp12934, tm12934, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12934, agent12934, scalar12934, tp12934, tm12934, ep12934, em12934, dsL]

theorem tails12934 :
    exp (-((12934:ℝ)*ep12934)) ≤ scalar12934.upperTail ∧
    exp (-((12934:ℝ)*em12934)) ≤ scalar12934.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12934:ℝ)) (by norm_num [ep12934]) ?_)
      (show bp12934^8 ≤ scalar12934.upperTail by norm_num [bp12934, scalar12934])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12934, bp12934, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12934:ℝ)) (by norm_num [em12934]) ?_)
      (show bm12934^8 ≤ scalar12934.lowerTail by norm_num [bm12934, scalar12934])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12934, bm12934, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12934 :
    agent12934.root+dsL+scalar12934.worldRadius < √(1/100/aL) ∧
    2*(agent12934.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12934, agent12934, scalar12934, tp12934, tm12934, ep12934, em12934, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12934, agent12934, scalar12934, tp12934, tm12934, ep12934, em12934, dsL]

noncomputable def master12934 : MasterCertificate 12934 world12934 agent12934 :=
  master scalar12934 dsL tp12934 tm12934 ep12934 em12934
    (by norm_num [dsL]) (by norm_num [tp12934]) (by norm_num [tm12934])
    (by norm_num [ep12934]) (by norm_num [em12934])
    positive12934 negative12934 tails12934.1 tails12934.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12934.1 tailGuards12934.2

theorem preserves12934 : master12934.toScalarCertificate = scalar12934 := rfl

noncomputable def tp12935 : ℝ := (2337292837 / 10000000000)
noncomputable def tm12935 : ℝ := (-((6108868889 / 10000000000)))
noncomputable def ep12935 : ℝ := (26020229137400103 / 50000000000000000000)
noncomputable def em12935 : ℝ := (12660917107155599 / 25000000000000000000)
noncomputable def bp12935 : ℝ := (21554699040378494147 / 50000000000000000000)
noncomputable def bm12935 : ℝ := (44094072901023825313 / 100000000000000000000)

theorem positive12935 :
    Eplus aL (agent12935.root+dsL) scalar12935.worldRadius world12935.frame
      agent12935.frame tp12935 ≤ -ep12935 := by
  apply positive_check (eT := (28914893231299171107 / 25000000000000000000)) (y := (38021157787280932953 / 100000000000000000000)) (u := (73129700461456781247 / 50000000000000000000))
  · norm_num [world12935, agent12935, scalar12935, tp12935, tm12935, ep12935, em12935, dsL]
  · norm_num [world12935, agent12935, scalar12935, tp12935, tm12935, ep12935, em12935, dsL]
  · norm_num [world12935, agent12935, scalar12935, tp12935, tm12935, ep12935, em12935, dsL]
  · norm_num [world12935, agent12935, scalar12935, tp12935, tm12935, ep12935, em12935, dsL]
  · norm_num [world12935, agent12935, scalar12935, tp12935, tm12935, ep12935, em12935, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12935, agent12935, tp12935, tm12935, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12935, agent12935, scalar12935, tp12935, tm12935, ep12935, em12935, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12935, agent12935, tp12935, tm12935, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12935, agent12935, scalar12935, tp12935, tm12935, ep12935, em12935, dsL]

theorem negative12935 :
    Eminus aL (agent12935.root+dsL) scalar12935.worldRadius world12935.frame
      agent12935.frame tm12935 ≤ -em12935 := by
  apply negative_check (lo := (68369965134681368941 / 100000000000000000000)) (hi := (34184982567340684471 / 50000000000000000000))
    (y := (-((71649874532267266589 / 100000000000000000000)))) (u := (48845948655335403197 / 100000000000000000000))
  · norm_num [world12935, agent12935, scalar12935, tp12935, tm12935, ep12935, em12935, dsL]
  · norm_num [world12935, agent12935, scalar12935, tp12935, tm12935, ep12935, em12935, dsL]
  · norm_num [world12935, agent12935, scalar12935, tp12935, tm12935, ep12935, em12935, dsL]
  · norm_num [world12935, agent12935, scalar12935, tp12935, tm12935, ep12935, em12935, dsL]
  · norm_num [world12935, agent12935, scalar12935, tp12935, tm12935, ep12935, em12935, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12935, agent12935, tp12935, tm12935, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12935, agent12935, tp12935, tm12935, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12935, agent12935, scalar12935, tp12935, tm12935, ep12935, em12935, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12935, agent12935, tp12935, tm12935, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12935, agent12935, scalar12935, tp12935, tm12935, ep12935, em12935, dsL]

theorem tails12935 :
    exp (-((12935:ℝ)*ep12935)) ≤ scalar12935.upperTail ∧
    exp (-((12935:ℝ)*em12935)) ≤ scalar12935.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12935:ℝ)) (by norm_num [ep12935]) ?_)
      (show bp12935^8 ≤ scalar12935.upperTail by norm_num [bp12935, scalar12935])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12935, bp12935, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12935:ℝ)) (by norm_num [em12935]) ?_)
      (show bm12935^8 ≤ scalar12935.lowerTail by norm_num [bm12935, scalar12935])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12935, bm12935, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12935 :
    agent12935.root+dsL+scalar12935.worldRadius < √(1/100/aL) ∧
    2*(agent12935.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12935, agent12935, scalar12935, tp12935, tm12935, ep12935, em12935, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12935, agent12935, scalar12935, tp12935, tm12935, ep12935, em12935, dsL]

noncomputable def master12935 : MasterCertificate 12935 world12935 agent12935 :=
  master scalar12935 dsL tp12935 tm12935 ep12935 em12935
    (by norm_num [dsL]) (by norm_num [tp12935]) (by norm_num [tm12935])
    (by norm_num [ep12935]) (by norm_num [em12935])
    positive12935 negative12935 tails12935.1 tails12935.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12935.1 tailGuards12935.2

theorem preserves12935 : master12935.toScalarCertificate = scalar12935 := rfl

noncomputable def tp12936 : ℝ := (1168685199 / 5000000000)
noncomputable def tm12936 : ℝ := (-((6109034231 / 10000000000)))
noncomputable def ep12936 : ℝ := (52042809257435993 / 100000000000000000000)
noncomputable def em12936 : ℝ := (1012913429197727 / 2000000000000000000)
noncomputable def bp12936 : ℝ := (43104955198128706653 / 100000000000000000000)
noncomputable def bm12936 : ℝ := (11022463395571508121 / 25000000000000000000)

theorem positive12936 :
    Eplus aL (agent12936.root+dsL) scalar12936.worldRadius world12936.frame
      agent12936.frame tp12936 ≤ -ep12936 := by
  apply positive_check (eT := (115659770778031319593 / 100000000000000000000)) (y := (38021863534236560749 / 100000000000000000000)) (u := (14626043314782533907 / 10000000000000000000))
  · norm_num [world12936, agent12936, scalar12936, tp12936, tm12936, ep12936, em12936, dsL]
  · norm_num [world12936, agent12936, scalar12936, tp12936, tm12936, ep12936, em12936, dsL]
  · norm_num [world12936, agent12936, scalar12936, tp12936, tm12936, ep12936, em12936, dsL]
  · norm_num [world12936, agent12936, scalar12936, tp12936, tm12936, ep12936, em12936, dsL]
  · norm_num [world12936, agent12936, scalar12936, tp12936, tm12936, ep12936, em12936, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12936, agent12936, tp12936, tm12936, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12936, agent12936, scalar12936, tp12936, tm12936, ep12936, em12936, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12936, agent12936, tp12936, tm12936, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12936, agent12936, scalar12936, tp12936, tm12936, ep12936, em12936, dsL]

theorem negative12936 :
    Eminus aL (agent12936.root+dsL) scalar12936.worldRadius world12936.frame
      agent12936.frame tm12936 ≤ -em12936 := by
  apply negative_check (lo := (68369818500955826477 / 100000000000000000000)) (hi := (34184909250477913239 / 50000000000000000000))
    (y := (-((71649847899484492901 / 100000000000000000000)))) (u := (24422980832186267327 / 50000000000000000000))
  · norm_num [world12936, agent12936, scalar12936, tp12936, tm12936, ep12936, em12936, dsL]
  · norm_num [world12936, agent12936, scalar12936, tp12936, tm12936, ep12936, em12936, dsL]
  · norm_num [world12936, agent12936, scalar12936, tp12936, tm12936, ep12936, em12936, dsL]
  · norm_num [world12936, agent12936, scalar12936, tp12936, tm12936, ep12936, em12936, dsL]
  · norm_num [world12936, agent12936, scalar12936, tp12936, tm12936, ep12936, em12936, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12936, agent12936, tp12936, tm12936, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12936, agent12936, tp12936, tm12936, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12936, agent12936, scalar12936, tp12936, tm12936, ep12936, em12936, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12936, agent12936, tp12936, tm12936, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12936, agent12936, scalar12936, tp12936, tm12936, ep12936, em12936, dsL]

theorem tails12936 :
    exp (-((12936:ℝ)*ep12936)) ≤ scalar12936.upperTail ∧
    exp (-((12936:ℝ)*em12936)) ≤ scalar12936.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12936:ℝ)) (by norm_num [ep12936]) ?_)
      (show bp12936^8 ≤ scalar12936.upperTail by norm_num [bp12936, scalar12936])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12936, bp12936, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12936:ℝ)) (by norm_num [em12936]) ?_)
      (show bm12936^8 ≤ scalar12936.lowerTail by norm_num [bm12936, scalar12936])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12936, bm12936, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12936 :
    agent12936.root+dsL+scalar12936.worldRadius < √(1/100/aL) ∧
    2*(agent12936.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12936, agent12936, scalar12936, tp12936, tm12936, ep12936, em12936, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12936, agent12936, scalar12936, tp12936, tm12936, ep12936, em12936, dsL]

noncomputable def master12936 : MasterCertificate 12936 world12936 agent12936 :=
  master scalar12936 dsL tp12936 tm12936 ep12936 em12936
    (by norm_num [dsL]) (by norm_num [tp12936]) (by norm_num [tm12936])
    (by norm_num [ep12936]) (by norm_num [em12936])
    positive12936 negative12936 tails12936.1 tails12936.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12936.1 tailGuards12936.2

theorem preserves12936 : master12936.toScalarCertificate = scalar12936 := rfl

noncomputable def tp12937 : ℝ := (467489599 / 2000000000)
noncomputable def tm12937 : ℝ := (-((6109199579 / 10000000000)))
noncomputable def ep12937 : ℝ := (52045158816347707 / 100000000000000000000)
noncomputable def em12937 : ℝ := (791369892822981 / 1562500000000000000)
noncomputable def bp12937 : ℝ := (5387564189048208781 / 12500000000000000000)
noncomputable def bm12937 : ℝ := (44085635409312086369 / 100000000000000000000)

theorem positive12937 :
    Eplus aL (agent12937.root+dsL) scalar12937.worldRadius world12937.frame
      agent12937.frame tp12937 ≤ -ep12937 := by
  apply positive_check (eT := (115659968922990875743 / 100000000000000000000)) (y := (1188205324828807783 / 3125000000000000000)) (u := (3656536675209858057 / 2500000000000000000))
  · norm_num [world12937, agent12937, scalar12937, tp12937, tm12937, ep12937, em12937, dsL]
  · norm_num [world12937, agent12937, scalar12937, tp12937, tm12937, ep12937, em12937, dsL]
  · norm_num [world12937, agent12937, scalar12937, tp12937, tm12937, ep12937, em12937, dsL]
  · norm_num [world12937, agent12937, scalar12937, tp12937, tm12937, ep12937, em12937, dsL]
  · norm_num [world12937, agent12937, scalar12937, tp12937, tm12937, ep12937, em12937, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12937, agent12937, tp12937, tm12937, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12937, agent12937, scalar12937, tp12937, tm12937, ep12937, em12937, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12937, agent12937, tp12937, tm12937, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12937, agent12937, scalar12937, tp12937, tm12937, ep12937, em12937, dsL]

theorem negative12937 :
    Eminus aL (agent12937.root+dsL) scalar12937.worldRadius world12937.frame
      agent12937.frame tm12937 ≤ -em12937 := by
  apply negative_check (lo := (68369671784783038423 / 100000000000000000000)) (hi := (8546208973097879803 / 12500000000000000000))
    (y := (-((17912455494846297791 / 25000000000000000000)))) (u := (4884597432529594381 / 10000000000000000000))
  · norm_num [world12937, agent12937, scalar12937, tp12937, tm12937, ep12937, em12937, dsL]
  · norm_num [world12937, agent12937, scalar12937, tp12937, tm12937, ep12937, em12937, dsL]
  · norm_num [world12937, agent12937, scalar12937, tp12937, tm12937, ep12937, em12937, dsL]
  · norm_num [world12937, agent12937, scalar12937, tp12937, tm12937, ep12937, em12937, dsL]
  · norm_num [world12937, agent12937, scalar12937, tp12937, tm12937, ep12937, em12937, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12937, agent12937, tp12937, tm12937, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12937, agent12937, tp12937, tm12937, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12937, agent12937, scalar12937, tp12937, tm12937, ep12937, em12937, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12937, agent12937, tp12937, tm12937, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12937, agent12937, scalar12937, tp12937, tm12937, ep12937, em12937, dsL]

theorem tails12937 :
    exp (-((12937:ℝ)*ep12937)) ≤ scalar12937.upperTail ∧
    exp (-((12937:ℝ)*em12937)) ≤ scalar12937.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12937:ℝ)) (by norm_num [ep12937]) ?_)
      (show bp12937^8 ≤ scalar12937.upperTail by norm_num [bp12937, scalar12937])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12937, bp12937, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12937:ℝ)) (by norm_num [em12937]) ?_)
      (show bm12937^8 ≤ scalar12937.lowerTail by norm_num [bm12937, scalar12937])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12937, bm12937, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12937 :
    agent12937.root+dsL+scalar12937.worldRadius < √(1/100/aL) ∧
    2*(agent12937.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12937, agent12937, scalar12937, tp12937, tm12937, ep12937, em12937, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12937, agent12937, scalar12937, tp12937, tm12937, ep12937, em12937, dsL]

noncomputable def master12937 : MasterCertificate 12937 world12937 agent12937 :=
  master scalar12937 dsL tp12937 tm12937 ep12937 em12937
    (by norm_num [dsL]) (by norm_num [tp12937]) (by norm_num [tm12937])
    (by norm_num [ep12937]) (by norm_num [em12937])
    positive12937 negative12937 tails12937.1 tails12937.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12937.1 tailGuards12937.2

theorem preserves12937 : master12937.toScalarCertificate = scalar12937 := rfl

noncomputable def tp12938 : ℝ := (2337525567 / 10000000000)
noncomputable def tm12938 : ℝ := (-((1527341199 / 2500000000)))
noncomputable def ep12938 : ℝ := (26023753634947903 / 50000000000000000000)
noncomputable def em12938 : ℝ := (2532483690257213 / 5000000000000000000)
noncomputable def bp12938 : ℝ := (43096072801594247427 / 100000000000000000000)
noncomputable def bm12938 : ℝ := (44081418143842603163 / 100000000000000000000)

theorem positive12938 :
    Eplus aL (agent12938.root+dsL) scalar12938.worldRadius world12938.frame
      agent12938.frame tp12938 ≤ -ep12938 := by
  apply positive_check (eT := (115660166920977320499 / 100000000000000000000)) (y := (950581927486837493 / 2500000000000000000)) (u := (29252500129815283629 / 20000000000000000000))
  · norm_num [world12938, agent12938, scalar12938, tp12938, tm12938, ep12938, em12938, dsL]
  · norm_num [world12938, agent12938, scalar12938, tp12938, tm12938, ep12938, em12938, dsL]
  · norm_num [world12938, agent12938, scalar12938, tp12938, tm12938, ep12938, em12938, dsL]
  · norm_num [world12938, agent12938, scalar12938, tp12938, tm12938, ep12938, em12938, dsL]
  · norm_num [world12938, agent12938, scalar12938, tp12938, tm12938, ep12938, em12938, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12938, agent12938, tp12938, tm12938, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12938, agent12938, scalar12938, tp12938, tm12938, ep12938, em12938, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12938, agent12938, tp12938, tm12938, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12938, agent12938, scalar12938, tp12938, tm12938, ep12938, em12938, dsL]

theorem negative12938 :
    Eminus aL (agent12938.root+dsL) scalar12938.worldRadius world12938.frame
      agent12938.frame tm12938 ≤ -em12938 := by
  apply negative_check (lo := (6836952556908911533 / 10000000000000000000)) (hi := (68369525569089115331 / 100000000000000000000))
    (y := (-((35824897644550265357 / 50000000000000000000)))) (u := (1953839494497091049 / 4000000000000000000))
  · norm_num [world12938, agent12938, scalar12938, tp12938, tm12938, ep12938, em12938, dsL]
  · norm_num [world12938, agent12938, scalar12938, tp12938, tm12938, ep12938, em12938, dsL]
  · norm_num [world12938, agent12938, scalar12938, tp12938, tm12938, ep12938, em12938, dsL]
  · norm_num [world12938, agent12938, scalar12938, tp12938, tm12938, ep12938, em12938, dsL]
  · norm_num [world12938, agent12938, scalar12938, tp12938, tm12938, ep12938, em12938, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12938, agent12938, tp12938, tm12938, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12938, agent12938, tp12938, tm12938, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12938, agent12938, scalar12938, tp12938, tm12938, ep12938, em12938, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12938, agent12938, tp12938, tm12938, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12938, agent12938, scalar12938, tp12938, tm12938, ep12938, em12938, dsL]

theorem tails12938 :
    exp (-((12938:ℝ)*ep12938)) ≤ scalar12938.upperTail ∧
    exp (-((12938:ℝ)*em12938)) ≤ scalar12938.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12938:ℝ)) (by norm_num [ep12938]) ?_)
      (show bp12938^8 ≤ scalar12938.upperTail by norm_num [bp12938, scalar12938])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12938, bp12938, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12938:ℝ)) (by norm_num [em12938]) ?_)
      (show bm12938^8 ≤ scalar12938.lowerTail by norm_num [bm12938, scalar12938])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12938, bm12938, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12938 :
    agent12938.root+dsL+scalar12938.worldRadius < √(1/100/aL) ∧
    2*(agent12938.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12938, agent12938, scalar12938, tp12938, tm12938, ep12938, em12938, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12938, agent12938, scalar12938, tp12938, tm12938, ep12938, em12938, dsL]

noncomputable def master12938 : MasterCertificate 12938 world12938 agent12938 :=
  master scalar12938 dsL tp12938 tm12938 ep12938 em12938
    (by norm_num [dsL]) (by norm_num [tp12938]) (by norm_num [tm12938])
    (by norm_num [ep12938]) (by norm_num [em12938])
    positive12938 negative12938 tails12938.1 tails12938.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12938.1 tailGuards12938.2

theorem preserves12938 : master12938.toScalarCertificate = scalar12938 := rfl

noncomputable def tp12939 : ℝ := (1168801541 / 5000000000)
noncomputable def tm12939 : ℝ := (-((381845621 / 625000000)))
noncomputable def ep12939 : ℝ := (52049854178427299 / 100000000000000000000)
noncomputable def em12939 : ℝ := (10130334610259437 / 20000000000000000000)
noncomputable def bp12939 : ℝ := (43091633372143616699 / 100000000000000000000)
noncomputable def bm12939 : ℝ := (22038601036226210057 / 50000000000000000000)

theorem positive12939 :
    Eplus aL (agent12939.root+dsL) scalar12939.worldRadius world12939.frame
      agent12939.frame tp12939 ≤ -ep12939 := by
  apply positive_check (eT := (57830182270787414541 / 50000000000000000000)) (y := (38023983240902554073 / 100000000000000000000)) (u := (146263533472835266099 / 100000000000000000000))
  · norm_num [world12939, agent12939, scalar12939, tp12939, tm12939, ep12939, em12939, dsL]
  · norm_num [world12939, agent12939, scalar12939, tp12939, tm12939, ep12939, em12939, dsL]
  · norm_num [world12939, agent12939, scalar12939, tp12939, tm12939, ep12939, em12939, dsL]
  · norm_num [world12939, agent12939, scalar12939, tp12939, tm12939, ep12939, em12939, dsL]
  · norm_num [world12939, agent12939, scalar12939, tp12939, tm12939, ep12939, em12939, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12939, agent12939, tp12939, tm12939, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12939, agent12939, scalar12939, tp12939, tm12939, ep12939, em12939, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12939, agent12939, tp12939, tm12939, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12939, agent12939, scalar12939, tp12939, tm12939, ep12939, em12939, dsL]

theorem negative12939 :
    Eminus aL (agent12939.root+dsL) scalar12939.worldRadius world12939.frame
      agent12939.frame tm12939 ≤ -em12939 := by
  apply negative_check (lo := (17092344906043439089 / 25000000000000000000)) (hi := (68369379624173756357 / 100000000000000000000))
    (y := (-((17912442158157579297 / 25000000000000000000)))) (u := (12211500095761270853 / 25000000000000000000))
  · norm_num [world12939, agent12939, scalar12939, tp12939, tm12939, ep12939, em12939, dsL]
  · norm_num [world12939, agent12939, scalar12939, tp12939, tm12939, ep12939, em12939, dsL]
  · norm_num [world12939, agent12939, scalar12939, tp12939, tm12939, ep12939, em12939, dsL]
  · norm_num [world12939, agent12939, scalar12939, tp12939, tm12939, ep12939, em12939, dsL]
  · norm_num [world12939, agent12939, scalar12939, tp12939, tm12939, ep12939, em12939, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12939, agent12939, tp12939, tm12939, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12939, agent12939, tp12939, tm12939, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12939, agent12939, scalar12939, tp12939, tm12939, ep12939, em12939, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12939, agent12939, tp12939, tm12939, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12939, agent12939, scalar12939, tp12939, tm12939, ep12939, em12939, dsL]

theorem tails12939 :
    exp (-((12939:ℝ)*ep12939)) ≤ scalar12939.upperTail ∧
    exp (-((12939:ℝ)*em12939)) ≤ scalar12939.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12939:ℝ)) (by norm_num [ep12939]) ?_)
      (show bp12939^8 ≤ scalar12939.upperTail by norm_num [bp12939, scalar12939])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12939, bp12939, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12939:ℝ)) (by norm_num [em12939]) ?_)
      (show bm12939^8 ≤ scalar12939.lowerTail by norm_num [bm12939, scalar12939])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12939, bm12939, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12939 :
    agent12939.root+dsL+scalar12939.worldRadius < √(1/100/aL) ∧
    2*(agent12939.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12939, agent12939, scalar12939, tp12939, tm12939, ep12939, em12939, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12939, agent12939, scalar12939, tp12939, tm12939, ep12939, em12939, dsL]

noncomputable def master12939 : MasterCertificate 12939 world12939 agent12939 :=
  master scalar12939 dsL tp12939 tm12939 ep12939 em12939
    (by norm_num [dsL]) (by norm_num [tp12939]) (by norm_num [tm12939])
    (by norm_num [ep12939]) (by norm_num [em12939])
    positive12939 negative12939 tails12939.1 tails12939.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12939.1 tailGuards12939.2

theorem preserves12939 : master12939.toScalarCertificate = scalar12939 := rfl

noncomputable def tp12940 : ℝ := (93510117 / 400000000)
noncomputable def tm12940 : ℝ := (-((1527478493 / 2500000000)))
noncomputable def ep12940 : ℝ := (52053571658155179 / 100000000000000000000)
noncomputable def em12940 : ℝ := (25327583889747373 / 50000000000000000000)
noncomputable def bp12940 : ℝ := (538577986978191539 / 1250000000000000000)
noncomputable def bm12940 : ℝ := (22035960048423318719 / 50000000000000000000)

theorem positive12940 :
    Eplus aL (agent12940.root+dsL) scalar12940.worldRadius world12940.frame
      agent12940.frame tp12940 ≤ -ep12940 := by
  apply positive_check (eT := (57830541418642773403 / 50000000000000000000)) (y := (38023972053491063953 / 100000000000000000000)) (u := (146263517109732831807 / 100000000000000000000))
  · norm_num [world12940, agent12940, scalar12940, tp12940, tm12940, ep12940, em12940, dsL]
  · norm_num [world12940, agent12940, scalar12940, tp12940, tm12940, ep12940, em12940, dsL]
  · norm_num [world12940, agent12940, scalar12940, tp12940, tm12940, ep12940, em12940, dsL]
  · norm_num [world12940, agent12940, scalar12940, tp12940, tm12940, ep12940, em12940, dsL]
  · norm_num [world12940, agent12940, scalar12940, tp12940, tm12940, ep12940, em12940, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12940, agent12940, tp12940, tm12940, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12940, agent12940, scalar12940, tp12940, tm12940, ep12940, em12940, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12940, agent12940, tp12940, tm12940, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12940, agent12940, scalar12940, tp12940, tm12940, ep12940, em12940, dsL]

theorem negative12940 :
    Eminus aL (agent12940.root+dsL) scalar12940.worldRadius world12940.frame
      agent12940.frame tm12940 ≤ -em12940 := by
  apply negative_check (lo := (68368302209615044123 / 100000000000000000000)) (hi := (17092075552403761031 / 25000000000000000000))
    (y := (-((71647863011495762219 / 100000000000000000000)))) (u := (1526466600363149137 / 3125000000000000000))
  · norm_num [world12940, agent12940, scalar12940, tp12940, tm12940, ep12940, em12940, dsL]
  · norm_num [world12940, agent12940, scalar12940, tp12940, tm12940, ep12940, em12940, dsL]
  · norm_num [world12940, agent12940, scalar12940, tp12940, tm12940, ep12940, em12940, dsL]
  · norm_num [world12940, agent12940, scalar12940, tp12940, tm12940, ep12940, em12940, dsL]
  · norm_num [world12940, agent12940, scalar12940, tp12940, tm12940, ep12940, em12940, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12940, agent12940, tp12940, tm12940, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12940, agent12940, tp12940, tm12940, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12940, agent12940, scalar12940, tp12940, tm12940, ep12940, em12940, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12940, agent12940, tp12940, tm12940, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12940, agent12940, scalar12940, tp12940, tm12940, ep12940, em12940, dsL]

theorem tails12940 :
    exp (-((12940:ℝ)*ep12940)) ≤ scalar12940.upperTail ∧
    exp (-((12940:ℝ)*em12940)) ≤ scalar12940.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12940:ℝ)) (by norm_num [ep12940]) ?_)
      (show bp12940^8 ≤ scalar12940.upperTail by norm_num [bp12940, scalar12940])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12940, bp12940, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12940:ℝ)) (by norm_num [em12940]) ?_)
      (show bm12940^8 ≤ scalar12940.lowerTail by norm_num [bm12940, scalar12940])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12940, bm12940, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12940 :
    agent12940.root+dsL+scalar12940.worldRadius < √(1/100/aL) ∧
    2*(agent12940.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12940, agent12940, scalar12940, tp12940, tm12940, ep12940, em12940, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12940, agent12940, scalar12940, tp12940, tm12940, ep12940, em12940, dsL]

noncomputable def master12940 : MasterCertificate 12940 world12940 agent12940 :=
  master scalar12940 dsL tp12940 tm12940 ep12940 em12940
    (by norm_num [dsL]) (by norm_num [tp12940]) (by norm_num [tm12940])
    (by norm_num [ep12940]) (by norm_num [em12940])
    positive12940 negative12940 tails12940.1 tails12940.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12940.1 tailGuards12940.2

theorem preserves12940 : master12940.toScalarCertificate = scalar12940 := rfl

noncomputable def tp12941 : ℝ := (1168915177 / 5000000000)
noncomputable def tm12941 : ℝ := (-((3055039501 / 5000000000)))
noncomputable def ep12941 : ℝ := (52055916303368081 / 100000000000000000000)
noncomputable def em12941 : ℝ := (25328582465100387 / 50000000000000000000)
noncomputable def bp12941 : ℝ := (43081801539770035851 / 100000000000000000000)
noncomputable def bm12941 : ℝ := (44067705904727257983 / 100000000000000000000)

theorem positive12941 :
    Eplus aL (agent12941.root+dsL) scalar12941.worldRadius world12941.frame
      agent12941.frame tp12941 ≤ -ep12941 := by
  apply positive_check (eT := (23132255978900703753 / 20000000000000000000)) (y := (38024677334380921961 / 100000000000000000000)) (u := (146264548682005577727 / 100000000000000000000))
  · norm_num [world12941, agent12941, scalar12941, tp12941, tm12941, ep12941, em12941, dsL]
  · norm_num [world12941, agent12941, scalar12941, tp12941, tm12941, ep12941, em12941, dsL]
  · norm_num [world12941, agent12941, scalar12941, tp12941, tm12941, ep12941, em12941, dsL]
  · norm_num [world12941, agent12941, scalar12941, tp12941, tm12941, ep12941, em12941, dsL]
  · norm_num [world12941, agent12941, scalar12941, tp12941, tm12941, ep12941, em12941, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12941, agent12941, tp12941, tm12941, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12941, agent12941, scalar12941, tp12941, tm12941, ep12941, em12941, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12941, agent12941, tp12941, tm12941, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12941, agent12941, scalar12941, tp12941, tm12941, ep12941, em12941, dsL]

theorem negative12941 :
    Eminus aL (agent12941.root+dsL) scalar12941.worldRadius world12941.frame
      agent12941.frame tm12941 ≤ -em12941 := by
  apply negative_check (lo := (34184078320419680663 / 50000000000000000000)) (hi := (68368156640839361327 / 100000000000000000000))
    (y := (-((71647836472983487631 / 100000000000000000000)))) (u := (48846944174871327867 / 100000000000000000000))
  · norm_num [world12941, agent12941, scalar12941, tp12941, tm12941, ep12941, em12941, dsL]
  · norm_num [world12941, agent12941, scalar12941, tp12941, tm12941, ep12941, em12941, dsL]
  · norm_num [world12941, agent12941, scalar12941, tp12941, tm12941, ep12941, em12941, dsL]
  · norm_num [world12941, agent12941, scalar12941, tp12941, tm12941, ep12941, em12941, dsL]
  · norm_num [world12941, agent12941, scalar12941, tp12941, tm12941, ep12941, em12941, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12941, agent12941, tp12941, tm12941, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12941, agent12941, tp12941, tm12941, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12941, agent12941, scalar12941, tp12941, tm12941, ep12941, em12941, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12941, agent12941, tp12941, tm12941, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12941, agent12941, scalar12941, tp12941, tm12941, ep12941, em12941, dsL]

theorem tails12941 :
    exp (-((12941:ℝ)*ep12941)) ≤ scalar12941.upperTail ∧
    exp (-((12941:ℝ)*em12941)) ≤ scalar12941.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12941:ℝ)) (by norm_num [ep12941]) ?_)
      (show bp12941^8 ≤ scalar12941.upperTail by norm_num [bp12941, scalar12941])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12941, bp12941, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12941:ℝ)) (by norm_num [em12941]) ?_)
      (show bm12941^8 ≤ scalar12941.lowerTail by norm_num [bm12941, scalar12941])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12941, bm12941, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12941 :
    agent12941.root+dsL+scalar12941.worldRadius < √(1/100/aL) ∧
    2*(agent12941.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12941, agent12941, scalar12941, tp12941, tm12941, ep12941, em12941, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12941, agent12941, scalar12941, tp12941, tm12941, ep12941, em12941, dsL]

noncomputable def master12941 : MasterCertificate 12941 world12941 agent12941 :=
  master scalar12941 dsL tp12941 tm12941 ep12941 em12941
    (by norm_num [dsL]) (by norm_num [tp12941]) (by norm_num [tm12941])
    (by norm_num [ep12941]) (by norm_num [em12941])
    positive12941 negative12941 tails12941.1 tails12941.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12941.1 tailGuards12941.2

theorem preserves12941 : master12941.toScalarCertificate = scalar12941 := rfl

noncomputable def tp12942 : ℝ := (233790777 / 1000000000)
noncomputable def tm12942 : ℝ := (-((3055121909 / 5000000000)))
noncomputable def ep12942 : ℝ := (26029130074538861 / 50000000000000000000)
noncomputable def em12942 : ℝ := (50659161325256977 / 100000000000000000000)
noncomputable def bp12942 : ℝ := (5384670610368661849 / 12500000000000000000)
noncomputable def bm12942 : ℝ := (4406349243422396523 / 10000000000000000000)

theorem positive12942 :
    Eplus aL (agent12942.root+dsL) scalar12942.worldRadius world12942.frame
      agent12942.frame tp12942 ≤ -ep12942 := by
  apply positive_check (eT := (115661476891130297503 / 100000000000000000000)) (y := (38025382670139546593 / 100000000000000000000)) (u := (29253116068361590263 / 20000000000000000000))
  · norm_num [world12942, agent12942, scalar12942, tp12942, tm12942, ep12942, em12942, dsL]
  · norm_num [world12942, agent12942, scalar12942, tp12942, tm12942, ep12942, em12942, dsL]
  · norm_num [world12942, agent12942, scalar12942, tp12942, tm12942, ep12942, em12942, dsL]
  · norm_num [world12942, agent12942, scalar12942, tp12942, tm12942, ep12942, em12942, dsL]
  · norm_num [world12942, agent12942, scalar12942, tp12942, tm12942, ep12942, em12942, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12942, agent12942, tp12942, tm12942, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12942, agent12942, scalar12942, tp12942, tm12942, ep12942, em12942, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12942, agent12942, tp12942, tm12942, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12942, agent12942, scalar12942, tp12942, tm12942, ep12942, em12942, dsL]

theorem negative12942 :
    Eminus aL (agent12942.root+dsL) scalar12942.worldRadius world12942.frame
      agent12942.frame tm12942 ≤ -em12942 := by
  apply negative_check (lo := (17092002981416139411 / 25000000000000000000)) (hi := (13673602385132911529 / 20000000000000000000))
    (y := (-((71647808366786518697 / 100000000000000000000)))) (u := (24423478951945800157 / 50000000000000000000))
  · norm_num [world12942, agent12942, scalar12942, tp12942, tm12942, ep12942, em12942, dsL]
  · norm_num [world12942, agent12942, scalar12942, tp12942, tm12942, ep12942, em12942, dsL]
  · norm_num [world12942, agent12942, scalar12942, tp12942, tm12942, ep12942, em12942, dsL]
  · norm_num [world12942, agent12942, scalar12942, tp12942, tm12942, ep12942, em12942, dsL]
  · norm_num [world12942, agent12942, scalar12942, tp12942, tm12942, ep12942, em12942, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12942, agent12942, tp12942, tm12942, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12942, agent12942, tp12942, tm12942, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12942, agent12942, scalar12942, tp12942, tm12942, ep12942, em12942, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12942, agent12942, tp12942, tm12942, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12942, agent12942, scalar12942, tp12942, tm12942, ep12942, em12942, dsL]

theorem tails12942 :
    exp (-((12942:ℝ)*ep12942)) ≤ scalar12942.upperTail ∧
    exp (-((12942:ℝ)*em12942)) ≤ scalar12942.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12942:ℝ)) (by norm_num [ep12942]) ?_)
      (show bp12942^8 ≤ scalar12942.upperTail by norm_num [bp12942, scalar12942])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12942, bp12942, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12942:ℝ)) (by norm_num [em12942]) ?_)
      (show bm12942^8 ≤ scalar12942.lowerTail by norm_num [bm12942, scalar12942])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12942, bm12942, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12942 :
    agent12942.root+dsL+scalar12942.worldRadius < √(1/100/aL) ∧
    2*(agent12942.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12942, agent12942, scalar12942, tp12942, tm12942, ep12942, em12942, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12942, agent12942, scalar12942, tp12942, tm12942, ep12942, em12942, dsL]

noncomputable def master12942 : MasterCertificate 12942 world12942 agent12942 :=
  master scalar12942 dsL tp12942 tm12942 ep12942 em12942
    (by norm_num [dsL]) (by norm_num [tp12942]) (by norm_num [tm12942])
    (by norm_num [ep12942]) (by norm_num [em12942])
    positive12942 negative12942 tails12942.1 tails12942.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12942.1 tailGuards12942.2

theorem preserves12942 : master12942.toScalarCertificate = scalar12942 := rfl

noncomputable def tp12943 : ℝ := (2337985133 / 10000000000)
noncomputable def tm12943 : ℝ := (-((6110408541 / 10000000000)))
noncomputable def ep12943 : ℝ := (13015150686526243 / 25000000000000000000)
noncomputable def em12943 : ℝ := (50661156554539919 / 100000000000000000000)
noncomputable def bp12943 : ℝ := (43072929300798780737 / 100000000000000000000)
noncomputable def bm12943 : ℝ := (44059279977677533649 / 100000000000000000000)

theorem positive12943 :
    Eplus aL (agent12943.root+dsL) scalar12943.worldRadius world12943.frame
      agent12943.frame tp12943 ≤ -ep12943 := by
  apply positive_check (eT := (23132334707851929873 / 20000000000000000000)) (y := (7605217502560425859 / 20000000000000000000)) (u := (36566652821913035839 / 25000000000000000000))
  · norm_num [world12943, agent12943, scalar12943, tp12943, tm12943, ep12943, em12943, dsL]
  · norm_num [world12943, agent12943, scalar12943, tp12943, tm12943, ep12943, em12943, dsL]
  · norm_num [world12943, agent12943, scalar12943, tp12943, tm12943, ep12943, em12943, dsL]
  · norm_num [world12943, agent12943, scalar12943, tp12943, tm12943, ep12943, em12943, dsL]
  · norm_num [world12943, agent12943, scalar12943, tp12943, tm12943, ep12943, em12943, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12943, agent12943, tp12943, tm12943, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12943, agent12943, scalar12943, tp12943, tm12943, ep12943, em12943, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12943, agent12943, tp12943, tm12943, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12943, agent12943, scalar12943, tp12943, tm12943, ep12943, em12943, dsL]

theorem negative12943 :
    Eminus aL (agent12943.root+dsL) scalar12943.worldRadius world12943.frame
      agent12943.frame tm12943 ≤ -em12943 := by
  apply negative_check (lo := (34183933774599441287 / 50000000000000000000)) (hi := (2734714701967955303 / 4000000000000000000))
    (y := (-((35823890071190603607 / 50000000000000000000)))) (u := (24423485845328463527 / 50000000000000000000))
  · norm_num [world12943, agent12943, scalar12943, tp12943, tm12943, ep12943, em12943, dsL]
  · norm_num [world12943, agent12943, scalar12943, tp12943, tm12943, ep12943, em12943, dsL]
  · norm_num [world12943, agent12943, scalar12943, tp12943, tm12943, ep12943, em12943, dsL]
  · norm_num [world12943, agent12943, scalar12943, tp12943, tm12943, ep12943, em12943, dsL]
  · norm_num [world12943, agent12943, scalar12943, tp12943, tm12943, ep12943, em12943, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12943, agent12943, tp12943, tm12943, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12943, agent12943, tp12943, tm12943, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12943, agent12943, scalar12943, tp12943, tm12943, ep12943, em12943, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12943, agent12943, tp12943, tm12943, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12943, agent12943, scalar12943, tp12943, tm12943, ep12943, em12943, dsL]

theorem tails12943 :
    exp (-((12943:ℝ)*ep12943)) ≤ scalar12943.upperTail ∧
    exp (-((12943:ℝ)*em12943)) ≤ scalar12943.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12943:ℝ)) (by norm_num [ep12943]) ?_)
      (show bp12943^8 ≤ scalar12943.upperTail by norm_num [bp12943, scalar12943])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12943, bp12943, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12943:ℝ)) (by norm_num [em12943]) ?_)
      (show bm12943^8 ≤ scalar12943.lowerTail by norm_num [bm12943, scalar12943])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12943, bm12943, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12943 :
    agent12943.root+dsL+scalar12943.worldRadius < √(1/100/aL) ∧
    2*(agent12943.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12943, agent12943, scalar12943, tp12943, tm12943, ep12943, em12943, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12943, agent12943, scalar12943, tp12943, tm12943, ep12943, em12943, dsL]

noncomputable def master12943 : MasterCertificate 12943 world12943 agent12943 :=
  master scalar12943 dsL tp12943 tm12943 ep12943 em12943
    (by norm_num [dsL]) (by norm_num [tp12943]) (by norm_num [tm12943])
    (by norm_num [ep12943]) (by norm_num [em12943])
    positive12943 negative12943 tails12943.1 tails12943.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12943.1 tailGuards12943.2

theorem preserves12943 : master12943.toScalarCertificate = scalar12943 := rfl

noncomputable def tp12944 : ℝ := (146128903 / 625000000)
noncomputable def tm12944 : ℝ := (-((763821657 / 1250000000)))
noncomputable def ep12944 : ℝ := (6507867915842861 / 12500000000000000000)
noncomputable def em12944 : ℝ := (25331574964358351 / 50000000000000000000)
noncomputable def bp12944 : ℝ := (43068495328257519637 / 100000000000000000000)
noncomputable def bm12944 : ℝ := (11013767256607714459 / 25000000000000000000)

theorem positive12944 :
    Eplus aL (agent12944.root+dsL) scalar12944.worldRadius world12944.frame
      agent12944.frame tp12944 ≤ -ep12944 := by
  apply positive_check (eT := (115661869874854802719 / 100000000000000000000)) (y := (38026791997958309183 / 100000000000000000000)) (u := (146267641717846721823 / 100000000000000000000))
  · norm_num [world12944, agent12944, scalar12944, tp12944, tm12944, ep12944, em12944, dsL]
  · norm_num [world12944, agent12944, scalar12944, tp12944, tm12944, ep12944, em12944, dsL]
  · norm_num [world12944, agent12944, scalar12944, tp12944, tm12944, ep12944, em12944, dsL]
  · norm_num [world12944, agent12944, scalar12944, tp12944, tm12944, ep12944, em12944, dsL]
  · norm_num [world12944, agent12944, scalar12944, tp12944, tm12944, ep12944, em12944, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12944, agent12944, tp12944, tm12944, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12944, agent12944, scalar12944, tp12944, tm12944, ep12944, em12944, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12944, agent12944, tp12944, tm12944, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12944, agent12944, scalar12944, tp12944, tm12944, ep12944, em12944, dsL]

theorem negative12944 :
    Eminus aL (agent12944.root+dsL) scalar12944.worldRadius world12944.frame
      agent12944.frame tm12944 ≤ -em12944 := by
  apply negative_check (lo := (17091930787462202869 / 25000000000000000000)) (hi := (68367723149848811477 / 100000000000000000000))
    (y := (-((71647752487730554051 / 100000000000000000000)))) (u := (48846985199118170613 / 100000000000000000000))
  · norm_num [world12944, agent12944, scalar12944, tp12944, tm12944, ep12944, em12944, dsL]
  · norm_num [world12944, agent12944, scalar12944, tp12944, tm12944, ep12944, em12944, dsL]
  · norm_num [world12944, agent12944, scalar12944, tp12944, tm12944, ep12944, em12944, dsL]
  · norm_num [world12944, agent12944, scalar12944, tp12944, tm12944, ep12944, em12944, dsL]
  · norm_num [world12944, agent12944, scalar12944, tp12944, tm12944, ep12944, em12944, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12944, agent12944, tp12944, tm12944, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12944, agent12944, tp12944, tm12944, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12944, agent12944, scalar12944, tp12944, tm12944, ep12944, em12944, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12944, agent12944, tp12944, tm12944, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12944, agent12944, scalar12944, tp12944, tm12944, ep12944, em12944, dsL]

theorem tails12944 :
    exp (-((12944:ℝ)*ep12944)) ≤ scalar12944.upperTail ∧
    exp (-((12944:ℝ)*em12944)) ≤ scalar12944.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12944:ℝ)) (by norm_num [ep12944]) ?_)
      (show bp12944^8 ≤ scalar12944.upperTail by norm_num [bp12944, scalar12944])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12944, bp12944, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12944:ℝ)) (by norm_num [em12944]) ?_)
      (show bm12944^8 ≤ scalar12944.lowerTail by norm_num [bm12944, scalar12944])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12944, bm12944, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12944 :
    agent12944.root+dsL+scalar12944.worldRadius < √(1/100/aL) ∧
    2*(agent12944.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12944, agent12944, scalar12944, tp12944, tm12944, ep12944, em12944, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12944, agent12944, scalar12944, tp12944, tm12944, ep12944, em12944, dsL]

noncomputable def master12944 : MasterCertificate 12944 world12944 agent12944 :=
  master scalar12944 dsL tp12944 tm12944 ep12944 em12944
    (by norm_num [dsL]) (by norm_num [tp12944]) (by norm_num [tm12944])
    (by norm_num [ep12944]) (by norm_num [em12944])
    positive12944 negative12944 tails12944.1 tails12944.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12944.1 tailGuards12944.2

theorem preserves12944 : master12944.toScalarCertificate = scalar12944 := rfl

noncomputable def tp12945 : ℝ := (1169069867 / 5000000000)
noncomputable def tm12945 : ℝ := (-((763842239 / 1250000000)))
noncomputable def ep12945 : ℝ := (10413056621591551 / 20000000000000000000)
noncomputable def em12945 : ℝ := (316657140921263 / 625000000000000000)
noncomputable def bp12945 : ℝ := (21532031058614507937 / 50000000000000000000)
noncomputable def bm12945 : ℝ := (44050858796632586917 / 100000000000000000000)

theorem positive12945 :
    Eplus aL (agent12945.root+dsL) scalar12945.worldRadius world12945.frame
      agent12945.frame tp12945 ≤ -ep12945 := by
  apply positive_check (eT := (2313241320693947891 / 2000000000000000000)) (y := (19013748129007411851 / 50000000000000000000)) (u := (29253734365210052487 / 20000000000000000000))
  · norm_num [world12945, agent12945, scalar12945, tp12945, tm12945, ep12945, em12945, dsL]
  · norm_num [world12945, agent12945, scalar12945, tp12945, tm12945, ep12945, em12945, dsL]
  · norm_num [world12945, agent12945, scalar12945, tp12945, tm12945, ep12945, em12945, dsL]
  · norm_num [world12945, agent12945, scalar12945, tp12945, tm12945, ep12945, em12945, dsL]
  · norm_num [world12945, agent12945, scalar12945, tp12945, tm12945, ep12945, em12945, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12945, agent12945, tp12945, tm12945, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12945, agent12945, scalar12945, tp12945, tm12945, ep12945, em12945, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12945, agent12945, tp12945, tm12945, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12945, agent12945, scalar12945, tp12945, tm12945, ep12945, em12945, dsL]

theorem negative12945 :
    Eminus aL (agent12945.root+dsL) scalar12945.worldRadius world12945.frame
      agent12945.frame tm12945 ≤ -em12945 := by
  apply negative_check (lo := (68367578944585627327 / 100000000000000000000)) (hi := (1068243421009150427 / 1562500000000000000))
    (y := (-((4477982797408551863 / 6250000000000000000)))) (u := (6105874842999400359 / 12500000000000000000))
  · norm_num [world12945, agent12945, scalar12945, tp12945, tm12945, ep12945, em12945, dsL]
  · norm_num [world12945, agent12945, scalar12945, tp12945, tm12945, ep12945, em12945, dsL]
  · norm_num [world12945, agent12945, scalar12945, tp12945, tm12945, ep12945, em12945, dsL]
  · norm_num [world12945, agent12945, scalar12945, tp12945, tm12945, ep12945, em12945, dsL]
  · norm_num [world12945, agent12945, scalar12945, tp12945, tm12945, ep12945, em12945, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12945, agent12945, tp12945, tm12945, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12945, agent12945, tp12945, tm12945, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12945, agent12945, scalar12945, tp12945, tm12945, ep12945, em12945, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12945, agent12945, tp12945, tm12945, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12945, agent12945, scalar12945, tp12945, tm12945, ep12945, em12945, dsL]

theorem tails12945 :
    exp (-((12945:ℝ)*ep12945)) ≤ scalar12945.upperTail ∧
    exp (-((12945:ℝ)*em12945)) ≤ scalar12945.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12945:ℝ)) (by norm_num [ep12945]) ?_)
      (show bp12945^8 ≤ scalar12945.upperTail by norm_num [bp12945, scalar12945])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12945, bp12945, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12945:ℝ)) (by norm_num [em12945]) ?_)
      (show bm12945^8 ≤ scalar12945.lowerTail by norm_num [bm12945, scalar12945])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12945, bm12945, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12945 :
    agent12945.root+dsL+scalar12945.worldRadius < √(1/100/aL) ∧
    2*(agent12945.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12945, agent12945, scalar12945, tp12945, tm12945, ep12945, em12945, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12945, agent12945, scalar12945, tp12945, tm12945, ep12945, em12945, dsL]

noncomputable def master12945 : MasterCertificate 12945 world12945 agent12945 :=
  master scalar12945 dsL tp12945 tm12945 ep12945 em12945
    (by norm_num [dsL]) (by norm_num [tp12945]) (by norm_num [tm12945])
    (by norm_num [ep12945]) (by norm_num [em12945])
    positive12945 negative12945 tails12945.1 tails12945.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12945.1 tailGuards12945.2

theorem preserves12945 : master12945.toScalarCertificate = scalar12945 := rfl

noncomputable def tp12946 : ℝ := (584554251 / 2500000000)
noncomputable def tm12946 : ℝ := (-((1222180477 / 2000000000)))
noncomputable def ep12946 : ℝ := (52067622264849111 / 100000000000000000000)
noncomputable def em12946 : ℝ := (5066713459523391 / 10000000000000000000)
noncomputable def bp12946 : ℝ := (21529814772844811061 / 50000000000000000000)
noncomputable def bm12946 : ℝ := (44046649156670512869 / 100000000000000000000)

theorem positive12946 :
    Eplus aL (agent12946.root+dsL) scalar12946.worldRadius world12946.frame
      agent12946.frame tp12946 ≤ -ep12946 := by
  apply positive_check (eT := (115662262112373200863 / 100000000000000000000)) (y := (38028200469845729743 / 100000000000000000000)) (u := (73134850935484507723 / 50000000000000000000))
  · norm_num [world12946, agent12946, scalar12946, tp12946, tm12946, ep12946, em12946, dsL]
  · norm_num [world12946, agent12946, scalar12946, tp12946, tm12946, ep12946, em12946, dsL]
  · norm_num [world12946, agent12946, scalar12946, tp12946, tm12946, ep12946, em12946, dsL]
  · norm_num [world12946, agent12946, scalar12946, tp12946, tm12946, ep12946, em12946, dsL]
  · norm_num [world12946, agent12946, scalar12946, tp12946, tm12946, ep12946, em12946, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12946, agent12946, tp12946, tm12946, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12946, agent12946, scalar12946, tp12946, tm12946, ep12946, em12946, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12946, agent12946, tp12946, tm12946, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12946, agent12946, scalar12946, tp12946, tm12946, ep12946, em12946, dsL]

theorem negative12946 :
    Eminus aL (agent12946.root+dsL) scalar12946.worldRadius world12946.frame
      agent12946.frame tm12946 ≤ -em12946 := by
  apply negative_check (lo := (68367435460932671261 / 100000000000000000000)) (hi := (34183717730466335631 / 50000000000000000000))
    (y := (-((35823847942179643027 / 50000000000000000000)))) (u := (1221175321204159531 / 2500000000000000000))
  · norm_num [world12946, agent12946, scalar12946, tp12946, tm12946, ep12946, em12946, dsL]
  · norm_num [world12946, agent12946, scalar12946, tp12946, tm12946, ep12946, em12946, dsL]
  · norm_num [world12946, agent12946, scalar12946, tp12946, tm12946, ep12946, em12946, dsL]
  · norm_num [world12946, agent12946, scalar12946, tp12946, tm12946, ep12946, em12946, dsL]
  · norm_num [world12946, agent12946, scalar12946, tp12946, tm12946, ep12946, em12946, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12946, agent12946, tp12946, tm12946, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12946, agent12946, tp12946, tm12946, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12946, agent12946, scalar12946, tp12946, tm12946, ep12946, em12946, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12946, agent12946, tp12946, tm12946, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12946, agent12946, scalar12946, tp12946, tm12946, ep12946, em12946, dsL]

theorem tails12946 :
    exp (-((12946:ℝ)*ep12946)) ≤ scalar12946.upperTail ∧
    exp (-((12946:ℝ)*em12946)) ≤ scalar12946.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12946:ℝ)) (by norm_num [ep12946]) ?_)
      (show bp12946^8 ≤ scalar12946.upperTail by norm_num [bp12946, scalar12946])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12946, bp12946, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12946:ℝ)) (by norm_num [em12946]) ?_)
      (show bm12946^8 ≤ scalar12946.lowerTail by norm_num [bm12946, scalar12946])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12946, bm12946, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12946 :
    agent12946.root+dsL+scalar12946.worldRadius < √(1/100/aL) ∧
    2*(agent12946.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12946, agent12946, scalar12946, tp12946, tm12946, ep12946, em12946, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12946, agent12946, scalar12946, tp12946, tm12946, ep12946, em12946, dsL]

noncomputable def master12946 : MasterCertificate 12946 world12946 agent12946 :=
  master scalar12946 dsL tp12946 tm12946 ep12946 em12946
    (by norm_num [dsL]) (by norm_num [tp12946]) (by norm_num [tm12946])
    (by norm_num [ep12946]) (by norm_num [em12946])
    positive12946 negative12946 tails12946.1 tails12946.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12946.1 tailGuards12946.2

theorem preserves12946 : master12946.toScalarCertificate = scalar12946 := rfl

noncomputable def tp12947 : ℝ := (1169147099 / 5000000000)
noncomputable def tm12947 : ℝ := (-((3055533383 / 5000000000)))
noncomputable def ep12947 : ℝ := (52069959400641407 / 100000000000000000000)
noncomputable def em12947 : ℝ := (50669124784046619 / 100000000000000000000)
noncomputable def bp12947 : ℝ := (10763799646725554299 / 25000000000000000000)
noncomputable def bm12947 : ℝ := (1761697640988594917 / 4000000000000000000)

theorem positive12947 :
    Eplus aL (agent12947.root+dsL) scalar12947.worldRadius world12947.frame
      agent12947.frame tp12947 ≤ -ep12947 := by
  apply positive_check (eT := (115662457676025462189 / 100000000000000000000)) (y := (38028903834488710503 / 100000000000000000000)) (u := (36567682670988379589 / 25000000000000000000))
  · norm_num [world12947, agent12947, scalar12947, tp12947, tm12947, ep12947, em12947, dsL]
  · norm_num [world12947, agent12947, scalar12947, tp12947, tm12947, ep12947, em12947, dsL]
  · norm_num [world12947, agent12947, scalar12947, tp12947, tm12947, ep12947, em12947, dsL]
  · norm_num [world12947, agent12947, scalar12947, tp12947, tm12947, ep12947, em12947, dsL]
  · norm_num [world12947, agent12947, scalar12947, tp12947, tm12947, ep12947, em12947, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12947, agent12947, tp12947, tm12947, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12947, agent12947, scalar12947, tp12947, tm12947, ep12947, em12947, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12947, agent12947, tp12947, tm12947, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12947, agent12947, scalar12947, tp12947, tm12947, ep12947, em12947, dsL]

theorem negative12947 :
    Eminus aL (agent12947.root+dsL) scalar12947.worldRadius world12947.frame
      agent12947.frame tm12947 ≤ -em12947 := by
  apply negative_check (lo := (17091823077931821701 / 25000000000000000000)) (hi := (13673458462345457361 / 20000000000000000000))
    (y := (-((35823833384837210429 / 50000000000000000000)))) (u := (2442351353491115417 / 5000000000000000000))
  · norm_num [world12947, agent12947, scalar12947, tp12947, tm12947, ep12947, em12947, dsL]
  · norm_num [world12947, agent12947, scalar12947, tp12947, tm12947, ep12947, em12947, dsL]
  · norm_num [world12947, agent12947, scalar12947, tp12947, tm12947, ep12947, em12947, dsL]
  · norm_num [world12947, agent12947, scalar12947, tp12947, tm12947, ep12947, em12947, dsL]
  · norm_num [world12947, agent12947, scalar12947, tp12947, tm12947, ep12947, em12947, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12947, agent12947, tp12947, tm12947, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12947, agent12947, tp12947, tm12947, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12947, agent12947, scalar12947, tp12947, tm12947, ep12947, em12947, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12947, agent12947, tp12947, tm12947, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12947, agent12947, scalar12947, tp12947, tm12947, ep12947, em12947, dsL]

theorem tails12947 :
    exp (-((12947:ℝ)*ep12947)) ≤ scalar12947.upperTail ∧
    exp (-((12947:ℝ)*em12947)) ≤ scalar12947.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12947:ℝ)) (by norm_num [ep12947]) ?_)
      (show bp12947^8 ≤ scalar12947.upperTail by norm_num [bp12947, scalar12947])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12947, bp12947, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12947:ℝ)) (by norm_num [em12947]) ?_)
      (show bm12947^8 ≤ scalar12947.lowerTail by norm_num [bm12947, scalar12947])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12947, bm12947, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12947 :
    agent12947.root+dsL+scalar12947.worldRadius < √(1/100/aL) ∧
    2*(agent12947.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12947, agent12947, scalar12947, tp12947, tm12947, ep12947, em12947, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12947, agent12947, scalar12947, tp12947, tm12947, ep12947, em12947, dsL]

noncomputable def master12947 : MasterCertificate 12947 world12947 agent12947 :=
  master scalar12947 dsL tp12947 tm12947 ep12947 em12947
    (by norm_num [dsL]) (by norm_num [tp12947]) (by norm_num [tm12947])
    (by norm_num [ep12947]) (by norm_num [em12947])
    positive12947 negative12947 tails12947.1 tails12947.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12947.1 tailGuards12947.2

theorem preserves12947 : master12947.toScalarCertificate = scalar12947 := rfl

noncomputable def tp12948 : ℝ := (1169185709 / 5000000000)
noncomputable def tm12948 : ℝ := (-((6111231057 / 10000000000)))
noncomputable def ep12948 : ℝ := (13018074018627653 / 25000000000000000000)
noncomputable def em12948 : ℝ := (5067111451284913 / 10000000000000000000)
noncomputable def bp12948 : ℝ := (43050768154391630039 / 100000000000000000000)
noncomputable def bm12948 : ℝ := (44038233403561369847 / 100000000000000000000)

theorem positive12948 :
    Eplus aL (agent12948.root+dsL) scalar12948.worldRadius world12948.frame
      agent12948.frame tp12948 ≤ -ep12948 := by
  apply positive_check (eT := (115662653459809687963 / 100000000000000000000)) (y := (9507402009442392333 / 25000000000000000000)) (u := (146271760730864738753 / 100000000000000000000))
  · norm_num [world12948, agent12948, scalar12948, tp12948, tm12948, ep12948, em12948, dsL]
  · norm_num [world12948, agent12948, scalar12948, tp12948, tm12948, ep12948, em12948, dsL]
  · norm_num [world12948, agent12948, scalar12948, tp12948, tm12948, ep12948, em12948, dsL]
  · norm_num [world12948, agent12948, scalar12948, tp12948, tm12948, ep12948, em12948, dsL]
  · norm_num [world12948, agent12948, scalar12948, tp12948, tm12948, ep12948, em12948, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12948, agent12948, tp12948, tm12948, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12948, agent12948, scalar12948, tp12948, tm12948, ep12948, em12948, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12948, agent12948, tp12948, tm12948, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12948, agent12948, scalar12948, tp12948, tm12948, ep12948, em12948, dsL]

theorem negative12948 :
    Eminus aL (agent12948.root+dsL) scalar12948.worldRadius world12948.frame
      agent12948.frame tm12948 ≤ -em12948 := by
  apply negative_check (lo := (68367149488426783377 / 100000000000000000000)) (hi := (34183574744213391689 / 50000000000000000000))
    (y := (-((35823818847854385081 / 50000000000000000000)))) (u := (9769408254318448903 / 20000000000000000000))
  · norm_num [world12948, agent12948, scalar12948, tp12948, tm12948, ep12948, em12948, dsL]
  · norm_num [world12948, agent12948, scalar12948, tp12948, tm12948, ep12948, em12948, dsL]
  · norm_num [world12948, agent12948, scalar12948, tp12948, tm12948, ep12948, em12948, dsL]
  · norm_num [world12948, agent12948, scalar12948, tp12948, tm12948, ep12948, em12948, dsL]
  · norm_num [world12948, agent12948, scalar12948, tp12948, tm12948, ep12948, em12948, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12948, agent12948, tp12948, tm12948, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12948, agent12948, tp12948, tm12948, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12948, agent12948, scalar12948, tp12948, tm12948, ep12948, em12948, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12948, agent12948, tp12948, tm12948, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12948, agent12948, scalar12948, tp12948, tm12948, ep12948, em12948, dsL]

theorem tails12948 :
    exp (-((12948:ℝ)*ep12948)) ≤ scalar12948.upperTail ∧
    exp (-((12948:ℝ)*em12948)) ≤ scalar12948.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12948:ℝ)) (by norm_num [ep12948]) ?_)
      (show bp12948^8 ≤ scalar12948.upperTail by norm_num [bp12948, scalar12948])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12948, bp12948, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12948:ℝ)) (by norm_num [em12948]) ?_)
      (show bm12948^8 ≤ scalar12948.lowerTail by norm_num [bm12948, scalar12948])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12948, bm12948, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12948 :
    agent12948.root+dsL+scalar12948.worldRadius < √(1/100/aL) ∧
    2*(agent12948.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12948, agent12948, scalar12948, tp12948, tm12948, ep12948, em12948, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12948, agent12948, scalar12948, tp12948, tm12948, ep12948, em12948, dsL]

noncomputable def master12948 : MasterCertificate 12948 world12948 agent12948 :=
  master scalar12948 dsL tp12948 tm12948 ep12948 em12948
    (by norm_num [dsL]) (by norm_num [tp12948]) (by norm_num [tm12948])
    (by norm_num [ep12948]) (by norm_num [em12948])
    positive12948 negative12948 tails12948.1 tails12948.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12948.1 tailGuards12948.2

theorem preserves12948 : master12948.toScalarCertificate = scalar12948 := rfl

noncomputable def tp12949 : ℝ := (1169224263 / 5000000000)
noncomputable def tm12949 : ℝ := (-((3055697731 / 5000000000)))
noncomputable def ep12949 : ℝ := (52074631171888949 / 100000000000000000000)
noncomputable def em12949 : ℝ := (12668275697238507 / 25000000000000000000)
noncomputable def bp12949 : ℝ := (5380792378093588057 / 12500000000000000000)
noncomputable def bm12949 : ℝ := (8806805400150026229 / 20000000000000000000)

theorem positive12949 :
    Eplus aL (agent12949.root+dsL) scalar12949.worldRadius world12949.frame
      agent12949.frame tp12949 ≤ -ep12949 := by
  apply positive_check (eT := (180723200735149069 / 156250000000000000)) (y := (38030310613291729193 / 100000000000000000000)) (u := (73136394202030775993 / 50000000000000000000))
  · norm_num [world12949, agent12949, scalar12949, tp12949, tm12949, ep12949, em12949, dsL]
  · norm_num [world12949, agent12949, scalar12949, tp12949, tm12949, ep12949, em12949, dsL]
  · norm_num [world12949, agent12949, scalar12949, tp12949, tm12949, ep12949, em12949, dsL]
  · norm_num [world12949, agent12949, scalar12949, tp12949, tm12949, ep12949, em12949, dsL]
  · norm_num [world12949, agent12949, scalar12949, tp12949, tm12949, ep12949, em12949, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12949, agent12949, tp12949, tm12949, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12949, agent12949, scalar12949, tp12949, tm12949, ep12949, em12949, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12949, agent12949, tp12949, tm12949, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12949, agent12949, scalar12949, tp12949, tm12949, ep12949, em12949, dsL]

theorem negative12949 :
    Eminus aL (agent12949.root+dsL) scalar12949.worldRadius world12949.frame
      agent12949.frame tm12949 ≤ -em12949 := by
  apply negative_check (lo := (17091751530799830389 / 25000000000000000000)) (hi := (68367006123199321557 / 100000000000000000000))
    (y := (-((71647610082108819959 / 100000000000000000000)))) (u := (48847054760020671083 / 100000000000000000000))
  · norm_num [world12949, agent12949, scalar12949, tp12949, tm12949, ep12949, em12949, dsL]
  · norm_num [world12949, agent12949, scalar12949, tp12949, tm12949, ep12949, em12949, dsL]
  · norm_num [world12949, agent12949, scalar12949, tp12949, tm12949, ep12949, em12949, dsL]
  · norm_num [world12949, agent12949, scalar12949, tp12949, tm12949, ep12949, em12949, dsL]
  · norm_num [world12949, agent12949, scalar12949, tp12949, tm12949, ep12949, em12949, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12949, agent12949, tp12949, tm12949, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12949, agent12949, tp12949, tm12949, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12949, agent12949, scalar12949, tp12949, tm12949, ep12949, em12949, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12949, agent12949, tp12949, tm12949, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12949, agent12949, scalar12949, tp12949, tm12949, ep12949, em12949, dsL]

theorem tails12949 :
    exp (-((12949:ℝ)*ep12949)) ≤ scalar12949.upperTail ∧
    exp (-((12949:ℝ)*em12949)) ≤ scalar12949.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12949:ℝ)) (by norm_num [ep12949]) ?_)
      (show bp12949^8 ≤ scalar12949.upperTail by norm_num [bp12949, scalar12949])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12949, bp12949, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12949:ℝ)) (by norm_num [em12949]) ?_)
      (show bm12949^8 ≤ scalar12949.lowerTail by norm_num [bm12949, scalar12949])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12949, bm12949, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12949 :
    agent12949.root+dsL+scalar12949.worldRadius < √(1/100/aL) ∧
    2*(agent12949.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12949, agent12949, scalar12949, tp12949, tm12949, ep12949, em12949, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12949, agent12949, scalar12949, tp12949, tm12949, ep12949, em12949, dsL]

noncomputable def master12949 : MasterCertificate 12949 world12949 agent12949 :=
  master scalar12949 dsL tp12949 tm12949 ep12949 em12949
    (by norm_num [dsL]) (by norm_num [tp12949]) (by norm_num [tm12949])
    (by norm_num [ep12949]) (by norm_num [em12949])
    positive12949 negative12949 tails12949.1 tails12949.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12949.1 tailGuards12949.2

theorem preserves12949 : master12949.toScalarCertificate = scalar12949 := rfl

end BstLean.Part268
