import BstLean.Part261Checker
import BstLean.Part268Scalar15
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12725 : ℝ := (2318765773 / 10000000000)
noncomputable def tm12725 : ℝ := (-((3033958711 / 5000000000)))
noncomputable def ep12725 : ℝ := (51492883955875371 / 100000000000000000000)
noncomputable def em12725 : ℝ := (5016881937556373 / 10000000000000000000)
noncomputable def bp12725 : ℝ := (4408464344310628863 / 10000000000000000000)
noncomputable def bm12725 : ℝ := (1800918077495323821 / 4000000000000000000)

theorem positive12725 :
    Eplus aL (agent12725.root+dsL) scalar12725.worldRadius world12725.frame
      agent12725.frame tp12725 ≤ -ep12725 := by
  apply positive_check (eT := (23120516086349735007 / 20000000000000000000)) (y := (37879624888696628797 / 100000000000000000000)) (u := (73026271087228760053 / 50000000000000000000))
  · norm_num [world12725, agent12725, scalar12725, tp12725, tm12725, ep12725, em12725, dsL]
  · norm_num [world12725, agent12725, scalar12725, tp12725, tm12725, ep12725, em12725, dsL]
  · norm_num [world12725, agent12725, scalar12725, tp12725, tm12725, ep12725, em12725, dsL]
  · norm_num [world12725, agent12725, scalar12725, tp12725, tm12725, ep12725, em12725, dsL]
  · norm_num [world12725, agent12725, scalar12725, tp12725, tm12725, ep12725, em12725, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12725, agent12725, tp12725, tm12725, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12725, agent12725, scalar12725, tp12725, tm12725, ep12725, em12725, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12725, agent12725, tp12725, tm12725, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12725, agent12725, scalar12725, tp12725, tm12725, ep12725, em12725, dsL]

theorem negative12725 :
    Eminus aL (agent12725.root+dsL) scalar12725.worldRadius world12725.frame
      agent12725.frame tm12725 ≤ -em12725 := by
  apply negative_check (lo := (34213060754447648139 / 50000000000000000000)) (hi := (68426121508895296279 / 100000000000000000000))
    (y := (-((71685482565080031347 / 100000000000000000000)))) (u := (48828558670210054247 / 100000000000000000000))
  · norm_num [world12725, agent12725, scalar12725, tp12725, tm12725, ep12725, em12725, dsL]
  · norm_num [world12725, agent12725, scalar12725, tp12725, tm12725, ep12725, em12725, dsL]
  · norm_num [world12725, agent12725, scalar12725, tp12725, tm12725, ep12725, em12725, dsL]
  · norm_num [world12725, agent12725, scalar12725, tp12725, tm12725, ep12725, em12725, dsL]
  · norm_num [world12725, agent12725, scalar12725, tp12725, tm12725, ep12725, em12725, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12725, agent12725, tp12725, tm12725, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12725, agent12725, tp12725, tm12725, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12725, agent12725, scalar12725, tp12725, tm12725, ep12725, em12725, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12725, agent12725, tp12725, tm12725, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12725, agent12725, scalar12725, tp12725, tm12725, ep12725, em12725, dsL]

theorem tails12725 :
    exp (-((12725:ℝ)*ep12725)) ≤ scalar12725.upperTail ∧
    exp (-((12725:ℝ)*em12725)) ≤ scalar12725.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12725:ℝ)) (by norm_num [ep12725]) ?_)
      (show bp12725^8 ≤ scalar12725.upperTail by norm_num [bp12725, scalar12725])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12725, bp12725, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12725:ℝ)) (by norm_num [em12725]) ?_)
      (show bm12725^8 ≤ scalar12725.lowerTail by norm_num [bm12725, scalar12725])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12725, bm12725, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12725 :
    agent12725.root+dsL+scalar12725.worldRadius < √(1/100/aL) ∧
    2*(agent12725.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12725, agent12725, scalar12725, tp12725, tm12725, ep12725, em12725, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12725, agent12725, scalar12725, tp12725, tm12725, ep12725, em12725, dsL]

noncomputable def master12725 : MasterCertificate 12725 world12725 agent12725 :=
  master scalar12725 dsL tp12725 tm12725 ep12725 em12725
    (by norm_num [dsL]) (by norm_num [tp12725]) (by norm_num [tm12725])
    (by norm_num [ep12725]) (by norm_num [em12725])
    positive12725 negative12725 tails12725.1 tails12725.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12725.1 tailGuards12725.2

theorem preserves12725 : master12725.toScalarCertificate = scalar12725 := rfl

noncomputable def tp12726 : ℝ := (2318850077 / 10000000000)
noncomputable def tm12726 : ℝ := (-((6068097989 / 10000000000)))
noncomputable def ep12726 : ℝ := (12873868217955633 / 25000000000000000000)
noncomputable def em12726 : ℝ := (25085519099864001 / 50000000000000000000)
noncomputable def bp12726 : ℝ := (22039995293026037881 / 50000000000000000000)
noncomputable def bm12726 : ℝ := (45018539590524602443 / 100000000000000000000)

theorem positive12726 :
    Eplus aL (agent12726.root+dsL) scalar12726.worldRadius world12726.frame
      agent12726.frame tp12726 ≤ -ep12726 := by
  apply positive_check (eT := (23120564047880542031 / 20000000000000000000)) (y := (37880411232240457121 / 100000000000000000000)) (u := (73026845326854498199 / 50000000000000000000))
  · norm_num [world12726, agent12726, scalar12726, tp12726, tm12726, ep12726, em12726, dsL]
  · norm_num [world12726, agent12726, scalar12726, tp12726, tm12726, ep12726, em12726, dsL]
  · norm_num [world12726, agent12726, scalar12726, tp12726, tm12726, ep12726, em12726, dsL]
  · norm_num [world12726, agent12726, scalar12726, tp12726, tm12726, ep12726, em12726, dsL]
  · norm_num [world12726, agent12726, scalar12726, tp12726, tm12726, ep12726, em12726, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12726, agent12726, tp12726, tm12726, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12726, agent12726, scalar12726, tp12726, tm12726, ep12726, em12726, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12726, agent12726, tp12726, tm12726, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12726, agent12726, scalar12726, tp12726, tm12726, ep12726, em12726, dsL]

theorem negative12726 :
    Eminus aL (agent12726.root+dsL) scalar12726.worldRadius world12726.frame
      agent12726.frame tm12726 ≤ -em12726 := by
  apply negative_check (lo := (68425921394734469713 / 100000000000000000000)) (hi := (34212960697367234857 / 50000000000000000000))
    (y := (-((2867421931280991401 / 4000000000000000000)))) (u := (48828526581583672761 / 100000000000000000000))
  · norm_num [world12726, agent12726, scalar12726, tp12726, tm12726, ep12726, em12726, dsL]
  · norm_num [world12726, agent12726, scalar12726, tp12726, tm12726, ep12726, em12726, dsL]
  · norm_num [world12726, agent12726, scalar12726, tp12726, tm12726, ep12726, em12726, dsL]
  · norm_num [world12726, agent12726, scalar12726, tp12726, tm12726, ep12726, em12726, dsL]
  · norm_num [world12726, agent12726, scalar12726, tp12726, tm12726, ep12726, em12726, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12726, agent12726, tp12726, tm12726, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12726, agent12726, tp12726, tm12726, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12726, agent12726, scalar12726, tp12726, tm12726, ep12726, em12726, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12726, agent12726, tp12726, tm12726, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12726, agent12726, scalar12726, tp12726, tm12726, ep12726, em12726, dsL]

theorem tails12726 :
    exp (-((12726:ℝ)*ep12726)) ≤ scalar12726.upperTail ∧
    exp (-((12726:ℝ)*em12726)) ≤ scalar12726.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12726:ℝ)) (by norm_num [ep12726]) ?_)
      (show bp12726^8 ≤ scalar12726.upperTail by norm_num [bp12726, scalar12726])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12726, bp12726, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12726:ℝ)) (by norm_num [em12726]) ?_)
      (show bm12726^8 ≤ scalar12726.lowerTail by norm_num [bm12726, scalar12726])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12726, bm12726, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12726 :
    agent12726.root+dsL+scalar12726.worldRadius < √(1/100/aL) ∧
    2*(agent12726.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12726, agent12726, scalar12726, tp12726, tm12726, ep12726, em12726, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12726, agent12726, scalar12726, tp12726, tm12726, ep12726, em12726, dsL]

noncomputable def master12726 : MasterCertificate 12726 world12726 agent12726 :=
  master scalar12726 dsL tp12726 tm12726 ep12726 em12726
    (by norm_num [dsL]) (by norm_num [tp12726]) (by norm_num [tm12726])
    (by norm_num [ep12726]) (by norm_num [em12726])
    positive12726 negative12726 tails12726.1 tails12726.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12726.1 tailGuards12726.2

theorem preserves12726 : master12726.toScalarCertificate = scalar12726 := rfl

noncomputable def tp12727 : ℝ := (289866791 / 1250000000)
noncomputable def tm12727 : ℝ := (-((3034139189 / 5000000000)))
noncomputable def ep12727 : ℝ := (205992240321231 / 400000000000000000)
noncomputable def em12727 : ℝ := (6271656931479451 / 12500000000000000000)
noncomputable def bp12727 : ℝ := (1763013565282141267 / 4000000000000000000)
noncomputable def bm12727 : ℝ := (45014128552168453737 / 100000000000000000000)

theorem positive12727 :
    Eplus aL (agent12727.root+dsL) scalar12727.worldRadius world12727.frame
      agent12727.frame tp12727 ≤ -ep12727 := by
  apply positive_check (eT := (57801529848364202529 / 50000000000000000000)) (y := (147973425812570311 / 390625000000000000)) (u := (18256854789092670941 / 12500000000000000000))
  · norm_num [world12727, agent12727, scalar12727, tp12727, tm12727, ep12727, em12727, dsL]
  · norm_num [world12727, agent12727, scalar12727, tp12727, tm12727, ep12727, em12727, dsL]
  · norm_num [world12727, agent12727, scalar12727, tp12727, tm12727, ep12727, em12727, dsL]
  · norm_num [world12727, agent12727, scalar12727, tp12727, tm12727, ep12727, em12727, dsL]
  · norm_num [world12727, agent12727, scalar12727, tp12727, tm12727, ep12727, em12727, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12727, agent12727, tp12727, tm12727, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12727, agent12727, scalar12727, tp12727, tm12727, ep12727, em12727, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12727, agent12727, tp12727, tm12727, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12727, agent12727, scalar12727, tp12727, tm12727, ep12727, em12727, dsL]

theorem negative12727 :
    Eminus aL (agent12727.root+dsL) scalar12727.worldRadius world12727.frame
      agent12727.frame tm12727 ≤ -em12727 := by
  apply negative_check (lo := (34212860992586800909 / 50000000000000000000)) (hi := (68425721985173601819 / 100000000000000000000))
    (y := (-((35842806347545087003 / 50000000000000000000)))) (u := (48828495129643046871 / 100000000000000000000))
  · norm_num [world12727, agent12727, scalar12727, tp12727, tm12727, ep12727, em12727, dsL]
  · norm_num [world12727, agent12727, scalar12727, tp12727, tm12727, ep12727, em12727, dsL]
  · norm_num [world12727, agent12727, scalar12727, tp12727, tm12727, ep12727, em12727, dsL]
  · norm_num [world12727, agent12727, scalar12727, tp12727, tm12727, ep12727, em12727, dsL]
  · norm_num [world12727, agent12727, scalar12727, tp12727, tm12727, ep12727, em12727, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12727, agent12727, tp12727, tm12727, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12727, agent12727, tp12727, tm12727, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12727, agent12727, scalar12727, tp12727, tm12727, ep12727, em12727, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12727, agent12727, tp12727, tm12727, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12727, agent12727, scalar12727, tp12727, tm12727, ep12727, em12727, dsL]

theorem tails12727 :
    exp (-((12727:ℝ)*ep12727)) ≤ scalar12727.upperTail ∧
    exp (-((12727:ℝ)*em12727)) ≤ scalar12727.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12727:ℝ)) (by norm_num [ep12727]) ?_)
      (show bp12727^8 ≤ scalar12727.upperTail by norm_num [bp12727, scalar12727])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12727, bp12727, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12727:ℝ)) (by norm_num [em12727]) ?_)
      (show bm12727^8 ≤ scalar12727.lowerTail by norm_num [bm12727, scalar12727])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12727, bm12727, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12727 :
    agent12727.root+dsL+scalar12727.worldRadius < √(1/100/aL) ∧
    2*(agent12727.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12727, agent12727, scalar12727, tp12727, tm12727, ep12727, em12727, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12727, agent12727, scalar12727, tp12727, tm12727, ep12727, em12727, dsL]

noncomputable def master12727 : MasterCertificate 12727 world12727 agent12727 :=
  master scalar12727 dsL tp12727 tm12727 ep12727 em12727
    (by norm_num [dsL]) (by norm_num [tp12727]) (by norm_num [tm12727])
    (by norm_num [ep12727]) (by norm_num [em12727])
    positive12727 negative12727 tails12727.1 tails12727.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12727.1 tailGuards12727.2

theorem preserves12727 : master12727.toScalarCertificate = scalar12727 := rfl

noncomputable def tp12728 : ℝ := (2319018543 / 10000000000)
noncomputable def tm12728 : ℝ := (-((6068458767 / 10000000000)))
noncomputable def ep12728 : ℝ := (1030012924384391 / 2000000000000000000)
noncomputable def em12728 : ℝ := (50175471682882151 / 100000000000000000000)
noncomputable def bp12728 : ℝ := (44070688633787415897 / 100000000000000000000)
noncomputable def bm12728 : ℝ := (1406553700865924737 / 3125000000000000000)

theorem positive12728 :
    Eplus aL (agent12728.root+dsL) scalar12728.worldRadius world12728.frame
      agent12728.frame tp12728 ≤ -ep12728 := by
  apply positive_check (eT := (4624131957066313471 / 4000000000000000000)) (y := (37881982617983590383 / 100000000000000000000)) (u := (36513996434653380001 / 25000000000000000000))
  · norm_num [world12728, agent12728, scalar12728, tp12728, tm12728, ep12728, em12728, dsL]
  · norm_num [world12728, agent12728, scalar12728, tp12728, tm12728, ep12728, em12728, dsL]
  · norm_num [world12728, agent12728, scalar12728, tp12728, tm12728, ep12728, em12728, dsL]
  · norm_num [world12728, agent12728, scalar12728, tp12728, tm12728, ep12728, em12728, dsL]
  · norm_num [world12728, agent12728, scalar12728, tp12728, tm12728, ep12728, em12728, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12728, agent12728, tp12728, tm12728, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12728, agent12728, scalar12728, tp12728, tm12728, ep12728, em12728, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12728, agent12728, tp12728, tm12728, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12728, agent12728, scalar12728, tp12728, tm12728, ep12728, em12728, dsL]

theorem negative12728 :
    Eminus aL (agent12728.root+dsL) scalar12728.worldRadius world12728.frame
      agent12728.frame tm12728 ≤ -em12728 := by
  apply negative_check (lo := (1069148789352816593 / 1562500000000000000)) (hi := (68425522518580261953 / 100000000000000000000))
    (y := (-((35842838975787952331 / 50000000000000000000)))) (u := (12207115816473371671 / 25000000000000000000))
  · norm_num [world12728, agent12728, scalar12728, tp12728, tm12728, ep12728, em12728, dsL]
  · norm_num [world12728, agent12728, scalar12728, tp12728, tm12728, ep12728, em12728, dsL]
  · norm_num [world12728, agent12728, scalar12728, tp12728, tm12728, ep12728, em12728, dsL]
  · norm_num [world12728, agent12728, scalar12728, tp12728, tm12728, ep12728, em12728, dsL]
  · norm_num [world12728, agent12728, scalar12728, tp12728, tm12728, ep12728, em12728, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12728, agent12728, tp12728, tm12728, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12728, agent12728, tp12728, tm12728, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12728, agent12728, scalar12728, tp12728, tm12728, ep12728, em12728, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12728, agent12728, tp12728, tm12728, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12728, agent12728, scalar12728, tp12728, tm12728, ep12728, em12728, dsL]

theorem tails12728 :
    exp (-((12728:ℝ)*ep12728)) ≤ scalar12728.upperTail ∧
    exp (-((12728:ℝ)*em12728)) ≤ scalar12728.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12728:ℝ)) (by norm_num [ep12728]) ?_)
      (show bp12728^8 ≤ scalar12728.upperTail by norm_num [bp12728, scalar12728])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12728, bp12728, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12728:ℝ)) (by norm_num [em12728]) ?_)
      (show bm12728^8 ≤ scalar12728.lowerTail by norm_num [bm12728, scalar12728])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12728, bm12728, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12728 :
    agent12728.root+dsL+scalar12728.worldRadius < √(1/100/aL) ∧
    2*(agent12728.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12728, agent12728, scalar12728, tp12728, tm12728, ep12728, em12728, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12728, agent12728, scalar12728, tp12728, tm12728, ep12728, em12728, dsL]

noncomputable def master12728 : MasterCertificate 12728 world12728 agent12728 :=
  master scalar12728 dsL tp12728 tm12728 ep12728 em12728
    (by norm_num [dsL]) (by norm_num [tp12728]) (by norm_num [tm12728])
    (by norm_num [ep12728]) (by norm_num [em12728])
    positive12728 negative12728 tails12728.1 tails12728.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12728.1 tailGuards12728.2

theorem preserves12728 : master12728.toScalarCertificate = scalar12728 := rfl

noncomputable def tp12729 : ℝ := (289887837 / 1250000000)
noncomputable def tm12729 : ℝ := (-((758579871 / 1250000000)))
noncomputable def ep12729 : ℝ := (51503231145031361 / 100000000000000000000)
noncomputable def em12729 : ℝ := (50177686805010477 / 100000000000000000000)
noncomputable def bp12729 : ℝ := (11016509797966142163 / 25000000000000000000)
noncomputable def bm12729 : ℝ := (45005309280050108027 / 100000000000000000000)

theorem positive12729 :
    Eplus aL (agent12729.root+dsL) scalar12729.worldRadius world12729.frame
      agent12729.frame tp12729 ≤ -ep12729 := by
  apply positive_check (eT := (28900884435302270731 / 25000000000000000000)) (y := (37882767554770930857 / 100000000000000000000)) (u := (18257141523784393709 / 12500000000000000000))
  · norm_num [world12729, agent12729, scalar12729, tp12729, tm12729, ep12729, em12729, dsL]
  · norm_num [world12729, agent12729, scalar12729, tp12729, tm12729, ep12729, em12729, dsL]
  · norm_num [world12729, agent12729, scalar12729, tp12729, tm12729, ep12729, em12729, dsL]
  · norm_num [world12729, agent12729, scalar12729, tp12729, tm12729, ep12729, em12729, dsL]
  · norm_num [world12729, agent12729, scalar12729, tp12729, tm12729, ep12729, em12729, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12729, agent12729, tp12729, tm12729, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12729, agent12729, scalar12729, tp12729, tm12729, ep12729, em12729, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12729, agent12729, tp12729, tm12729, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12729, agent12729, scalar12729, tp12729, tm12729, ep12729, em12729, dsL]

theorem negative12729 :
    Eminus aL (agent12729.root+dsL) scalar12729.worldRadius world12729.frame
      agent12729.frame tm12729 ≤ -em12729 := by
  apply negative_check (lo := (68425323799359867593 / 100000000000000000000)) (hi := (34212661899679933797 / 50000000000000000000))
    (y := (-((71685742346745955523 / 100000000000000000000)))) (u := (48828431822731657329 / 100000000000000000000))
  · norm_num [world12729, agent12729, scalar12729, tp12729, tm12729, ep12729, em12729, dsL]
  · norm_num [world12729, agent12729, scalar12729, tp12729, tm12729, ep12729, em12729, dsL]
  · norm_num [world12729, agent12729, scalar12729, tp12729, tm12729, ep12729, em12729, dsL]
  · norm_num [world12729, agent12729, scalar12729, tp12729, tm12729, ep12729, em12729, dsL]
  · norm_num [world12729, agent12729, scalar12729, tp12729, tm12729, ep12729, em12729, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12729, agent12729, tp12729, tm12729, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12729, agent12729, tp12729, tm12729, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12729, agent12729, scalar12729, tp12729, tm12729, ep12729, em12729, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12729, agent12729, tp12729, tm12729, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12729, agent12729, scalar12729, tp12729, tm12729, ep12729, em12729, dsL]

theorem tails12729 :
    exp (-((12729:ℝ)*ep12729)) ≤ scalar12729.upperTail ∧
    exp (-((12729:ℝ)*em12729)) ≤ scalar12729.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12729:ℝ)) (by norm_num [ep12729]) ?_)
      (show bp12729^8 ≤ scalar12729.upperTail by norm_num [bp12729, scalar12729])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12729, bp12729, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12729:ℝ)) (by norm_num [em12729]) ?_)
      (show bm12729^8 ≤ scalar12729.lowerTail by norm_num [bm12729, scalar12729])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12729, bm12729, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12729 :
    agent12729.root+dsL+scalar12729.worldRadius < √(1/100/aL) ∧
    2*(agent12729.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12729, agent12729, scalar12729, tp12729, tm12729, ep12729, em12729, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12729, agent12729, scalar12729, tp12729, tm12729, ep12729, em12729, dsL]

noncomputable def master12729 : MasterCertificate 12729 world12729 agent12729 :=
  master scalar12729 dsL tp12729 tm12729 ep12729 em12729
    (by norm_num [dsL]) (by norm_num [tp12729]) (by norm_num [tm12729])
    (by norm_num [ep12729]) (by norm_num [em12729])
    positive12729 negative12729 tails12729.1 tails12729.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12729.1 tailGuards12729.2

theorem preserves12729 : master12729.toScalarCertificate = scalar12729 := rfl

noncomputable def tp12730 : ℝ := (1159630473 / 5000000000)
noncomputable def tm12730 : ℝ := (-((6069043329 / 10000000000)))
noncomputable def ep12730 : ℝ := (2575361484119787 / 5000000000000000000)
noncomputable def em12730 : ℝ := (25090721192284443 / 50000000000000000000)
noncomputable def bp12730 : ℝ := (5507549855728096271 / 12500000000000000000)
noncomputable def bm12730 : ℝ := (44999797242756149253 / 100000000000000000000)

theorem positive12730 :
    Eplus aL (agent12730.root+dsL) scalar12730.worldRadius world12730.frame
      agent12730.frame tp12730 ≤ -ep12730 := by
  apply positive_check (eT := (14450539017510830333 / 12500000000000000000)) (y := (37882828193710091553 / 100000000000000000000)) (u := (146057220757797531591 / 100000000000000000000))
  · norm_num [world12730, agent12730, scalar12730, tp12730, tm12730, ep12730, em12730, dsL]
  · norm_num [world12730, agent12730, scalar12730, tp12730, tm12730, ep12730, em12730, dsL]
  · norm_num [world12730, agent12730, scalar12730, tp12730, tm12730, ep12730, em12730, dsL]
  · norm_num [world12730, agent12730, scalar12730, tp12730, tm12730, ep12730, em12730, dsL]
  · norm_num [world12730, agent12730, scalar12730, tp12730, tm12730, ep12730, em12730, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12730, agent12730, tp12730, tm12730, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12730, agent12730, scalar12730, tp12730, tm12730, ep12730, em12730, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12730, agent12730, tp12730, tm12730, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12730, agent12730, scalar12730, tp12730, tm12730, ep12730, em12730, dsL]

theorem negative12730 :
    Eminus aL (agent12730.root+dsL) scalar12730.worldRadius world12730.frame
      agent12730.frame tm12730 ≤ -em12730 := by
  apply negative_check (lo := (8553020758502247699 / 12500000000000000000)) (hi := (68424166068017981593 / 100000000000000000000))
    (y := (-((71683903590219054909 / 100000000000000000000)))) (u := (48829329666963340433 / 100000000000000000000))
  · norm_num [world12730, agent12730, scalar12730, tp12730, tm12730, ep12730, em12730, dsL]
  · norm_num [world12730, agent12730, scalar12730, tp12730, tm12730, ep12730, em12730, dsL]
  · norm_num [world12730, agent12730, scalar12730, tp12730, tm12730, ep12730, em12730, dsL]
  · norm_num [world12730, agent12730, scalar12730, tp12730, tm12730, ep12730, em12730, dsL]
  · norm_num [world12730, agent12730, scalar12730, tp12730, tm12730, ep12730, em12730, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12730, agent12730, tp12730, tm12730, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12730, agent12730, tp12730, tm12730, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12730, agent12730, scalar12730, tp12730, tm12730, ep12730, em12730, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12730, agent12730, tp12730, tm12730, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12730, agent12730, scalar12730, tp12730, tm12730, ep12730, em12730, dsL]

theorem tails12730 :
    exp (-((12730:ℝ)*ep12730)) ≤ scalar12730.upperTail ∧
    exp (-((12730:ℝ)*em12730)) ≤ scalar12730.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12730:ℝ)) (by norm_num [ep12730]) ?_)
      (show bp12730^8 ≤ scalar12730.upperTail by norm_num [bp12730, scalar12730])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12730, bp12730, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12730:ℝ)) (by norm_num [em12730]) ?_)
      (show bm12730^8 ≤ scalar12730.lowerTail by norm_num [bm12730, scalar12730])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12730, bm12730, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12730 :
    agent12730.root+dsL+scalar12730.worldRadius < √(1/100/aL) ∧
    2*(agent12730.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12730, agent12730, scalar12730, tp12730, tm12730, ep12730, em12730, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12730, agent12730, scalar12730, tp12730, tm12730, ep12730, em12730, dsL]

noncomputable def master12730 : MasterCertificate 12730 world12730 agent12730 :=
  master scalar12730 dsL tp12730 tm12730 ep12730 em12730
    (by norm_num [dsL]) (by norm_num [tp12730]) (by norm_num [tm12730])
    (by norm_num [ep12730]) (by norm_num [em12730])
    positive12730 negative12730 tails12730.1 tails12730.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12730.1 tailGuards12730.2

theorem preserves12730 : master12730.toScalarCertificate = scalar12730 := rfl

noncomputable def tp12731 : ℝ := (2319345001 / 10000000000)
noncomputable def tm12731 : ℝ := (-((1517305829 / 2500000000)))
noncomputable def ep12731 : ℝ := (12877452906397741 / 25000000000000000000)
noncomputable def em12731 : ℝ := (50183654749770997 / 100000000000000000000)
noncomputable def bp12731 : ℝ := (44055751933308746903 / 100000000000000000000)
noncomputable def bm12731 : ℝ := (4499539045606600221 / 10000000000000000000)

theorem positive12731 :
    Eplus aL (agent12731.root+dsL) scalar12731.worldRadius world12731.frame
      agent12731.frame tp12731 ≤ -ep12731 := by
  apply positive_check (eT := (57802275150622977329 / 50000000000000000000)) (y := (37883612156062932381 / 100000000000000000000)) (u := (146058365795910206343 / 100000000000000000000))
  · norm_num [world12731, agent12731, scalar12731, tp12731, tm12731, ep12731, em12731, dsL]
  · norm_num [world12731, agent12731, scalar12731, tp12731, tm12731, ep12731, em12731, dsL]
  · norm_num [world12731, agent12731, scalar12731, tp12731, tm12731, ep12731, em12731, dsL]
  · norm_num [world12731, agent12731, scalar12731, tp12731, tm12731, ep12731, em12731, dsL]
  · norm_num [world12731, agent12731, scalar12731, tp12731, tm12731, ep12731, em12731, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12731, agent12731, tp12731, tm12731, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12731, agent12731, scalar12731, tp12731, tm12731, ep12731, em12731, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12731, agent12731, tp12731, tm12731, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12731, agent12731, scalar12731, tp12731, tm12731, ep12731, em12731, dsL]

theorem negative12731 :
    Eminus aL (agent12731.root+dsL) scalar12731.worldRadius world12731.frame
      agent12731.frame tm12731 ≤ -em12731 := by
  apply negative_check (lo := (68423968174157374249 / 100000000000000000000)) (hi := (273695872696629497 / 400000000000000000))
    (y := (-((3584198353137180123 / 5000000000000000000)))) (u := (48829298673764917249 / 100000000000000000000))
  · norm_num [world12731, agent12731, scalar12731, tp12731, tm12731, ep12731, em12731, dsL]
  · norm_num [world12731, agent12731, scalar12731, tp12731, tm12731, ep12731, em12731, dsL]
  · norm_num [world12731, agent12731, scalar12731, tp12731, tm12731, ep12731, em12731, dsL]
  · norm_num [world12731, agent12731, scalar12731, tp12731, tm12731, ep12731, em12731, dsL]
  · norm_num [world12731, agent12731, scalar12731, tp12731, tm12731, ep12731, em12731, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12731, agent12731, tp12731, tm12731, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12731, agent12731, tp12731, tm12731, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12731, agent12731, scalar12731, tp12731, tm12731, ep12731, em12731, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12731, agent12731, tp12731, tm12731, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12731, agent12731, scalar12731, tp12731, tm12731, ep12731, em12731, dsL]

theorem tails12731 :
    exp (-((12731:ℝ)*ep12731)) ≤ scalar12731.upperTail ∧
    exp (-((12731:ℝ)*em12731)) ≤ scalar12731.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12731:ℝ)) (by norm_num [ep12731]) ?_)
      (show bp12731^8 ≤ scalar12731.upperTail by norm_num [bp12731, scalar12731])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12731, bp12731, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12731:ℝ)) (by norm_num [em12731]) ?_)
      (show bm12731^8 ≤ scalar12731.lowerTail by norm_num [bm12731, scalar12731])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12731, bm12731, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12731 :
    agent12731.root+dsL+scalar12731.worldRadius < √(1/100/aL) ∧
    2*(agent12731.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12731, agent12731, scalar12731, tp12731, tm12731, ep12731, em12731, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12731, agent12731, scalar12731, tp12731, tm12731, ep12731, em12731, dsL]

noncomputable def master12731 : MasterCertificate 12731 world12731 agent12731 :=
  master scalar12731 dsL tp12731 tm12731 ep12731 em12731
    (by norm_num [dsL]) (by norm_num [tp12731]) (by norm_num [tm12731])
    (by norm_num [ep12731]) (by norm_num [em12731])
    positive12731 negative12731 tails12731.1 tails12731.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12731.1 tailGuards12731.2

theorem preserves12731 : master12731.toScalarCertificate = scalar12731 := rfl

noncomputable def tp12732 : ℝ := (2319429047 / 10000000000)
noncomputable def tm12732 : ℝ := (-((1213880673 / 2000000000)))
noncomputable def ep12732 : ℝ := (51512393118492803 / 100000000000000000000)
noncomputable def em12732 : ℝ := (10037173336762121 / 20000000000000000000)
noncomputable def bp12732 : ℝ := (44051105542233117633 / 100000000000000000000)
noncomputable def bm12732 : ℝ := (44990984160812940223 / 100000000000000000000)

theorem positive12732 :
    Eplus aL (agent12732.root+dsL) scalar12732.worldRadius world12732.frame
      agent12732.frame tp12732 ≤ -ep12732 := by
  apply positive_check (eT := (57802394215073624969 / 50000000000000000000)) (y := (7576879244996495849 / 20000000000000000000)) (u := (146059510998650393651 / 100000000000000000000))
  · norm_num [world12732, agent12732, scalar12732, tp12732, tm12732, ep12732, em12732, dsL]
  · norm_num [world12732, agent12732, scalar12732, tp12732, tm12732, ep12732, em12732, dsL]
  · norm_num [world12732, agent12732, scalar12732, tp12732, tm12732, ep12732, em12732, dsL]
  · norm_num [world12732, agent12732, scalar12732, tp12732, tm12732, ep12732, em12732, dsL]
  · norm_num [world12732, agent12732, scalar12732, tp12732, tm12732, ep12732, em12732, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12732, agent12732, tp12732, tm12732, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12732, agent12732, scalar12732, tp12732, tm12732, ep12732, em12732, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12732, agent12732, tp12732, tm12732, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12732, agent12732, scalar12732, tp12732, tm12732, ep12732, em12732, dsL]

theorem negative12732 :
    Eminus aL (agent12732.root+dsL) scalar12732.worldRadius world12732.frame
      agent12732.frame tm12732 ≤ -em12732 := by
  apply negative_check (lo := (34211884979045373483 / 50000000000000000000)) (hi := (68423769958090746967 / 100000000000000000000))
    (y := (-((35842015910204374363 / 50000000000000000000)))) (u := (24414633526530713619 / 50000000000000000000))
  · norm_num [world12732, agent12732, scalar12732, tp12732, tm12732, ep12732, em12732, dsL]
  · norm_num [world12732, agent12732, scalar12732, tp12732, tm12732, ep12732, em12732, dsL]
  · norm_num [world12732, agent12732, scalar12732, tp12732, tm12732, ep12732, em12732, dsL]
  · norm_num [world12732, agent12732, scalar12732, tp12732, tm12732, ep12732, em12732, dsL]
  · norm_num [world12732, agent12732, scalar12732, tp12732, tm12732, ep12732, em12732, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12732, agent12732, tp12732, tm12732, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12732, agent12732, tp12732, tm12732, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12732, agent12732, scalar12732, tp12732, tm12732, ep12732, em12732, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12732, agent12732, tp12732, tm12732, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12732, agent12732, scalar12732, tp12732, tm12732, ep12732, em12732, dsL]

theorem tails12732 :
    exp (-((12732:ℝ)*ep12732)) ≤ scalar12732.upperTail ∧
    exp (-((12732:ℝ)*em12732)) ≤ scalar12732.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12732:ℝ)) (by norm_num [ep12732]) ?_)
      (show bp12732^8 ≤ scalar12732.upperTail by norm_num [bp12732, scalar12732])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12732, bp12732, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12732:ℝ)) (by norm_num [em12732]) ?_)
      (show bm12732^8 ≤ scalar12732.lowerTail by norm_num [bm12732, scalar12732])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12732, bm12732, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12732 :
    agent12732.root+dsL+scalar12732.worldRadius < √(1/100/aL) ∧
    2*(agent12732.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12732, agent12732, scalar12732, tp12732, tm12732, ep12732, em12732, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12732, agent12732, scalar12732, tp12732, tm12732, ep12732, em12732, dsL]

noncomputable def master12732 : MasterCertificate 12732 world12732 agent12732 :=
  master scalar12732 dsL tp12732 tm12732 ep12732 em12732
    (by norm_num [dsL]) (by norm_num [tp12732]) (by norm_num [tm12732])
    (by norm_num [ep12732]) (by norm_num [em12732])
    positive12732 negative12732 tails12732.1 tails12732.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12732.1 tailGuards12732.2

theorem preserves12732 : master12732.toScalarCertificate = scalar12732 := rfl

noncomputable def tp12733 : ℝ := (2319513007 / 10000000000)
noncomputable def tm12733 : ℝ := (-((3034791593 / 5000000000)))
noncomputable def ep12733 : ℝ := (25757486298024781 / 50000000000000000000)
noncomputable def em12733 : ℝ := (50188076783552707 / 100000000000000000000)
noncomputable def bp12733 : ℝ := (11011615192449285833 / 25000000000000000000)
noncomputable def bm12733 : ℝ := (44986579361679253151 / 100000000000000000000)

theorem positive12733 :
    Eplus aL (agent12733.root+dsL) scalar12733.worldRadius world12733.frame
      agent12733.frame tp12733 ≤ -ep12733 := by
  apply positive_check (eT := (57802512985149782617 / 50000000000000000000)) (y := (37885179145303203649 / 100000000000000000000)) (u := (73030327266359413619 / 50000000000000000000))
  · norm_num [world12733, agent12733, scalar12733, tp12733, tm12733, ep12733, em12733, dsL]
  · norm_num [world12733, agent12733, scalar12733, tp12733, tm12733, ep12733, em12733, dsL]
  · norm_num [world12733, agent12733, scalar12733, tp12733, tm12733, ep12733, em12733, dsL]
  · norm_num [world12733, agent12733, scalar12733, tp12733, tm12733, ep12733, em12733, dsL]
  · norm_num [world12733, agent12733, scalar12733, tp12733, tm12733, ep12733, em12733, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12733, agent12733, tp12733, tm12733, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12733, agent12733, scalar12733, tp12733, tm12733, ep12733, em12733, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12733, agent12733, tp12733, tm12733, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12733, agent12733, scalar12733, tp12733, tm12733, ep12733, em12733, dsL]

theorem negative12733 :
    Eminus aL (agent12733.root+dsL) scalar12733.worldRadius world12733.frame
      agent12733.frame tm12733 ≤ -em12733 := by
  apply negative_check (lo := (34211786330173508471 / 50000000000000000000)) (hi := (68423572660347016943 / 100000000000000000000))
    (y := (-((7168409478384681629 / 10000000000000000000)))) (u := (1220730907712144659 / 2500000000000000000))
  · norm_num [world12733, agent12733, scalar12733, tp12733, tm12733, ep12733, em12733, dsL]
  · norm_num [world12733, agent12733, scalar12733, tp12733, tm12733, ep12733, em12733, dsL]
  · norm_num [world12733, agent12733, scalar12733, tp12733, tm12733, ep12733, em12733, dsL]
  · norm_num [world12733, agent12733, scalar12733, tp12733, tm12733, ep12733, em12733, dsL]
  · norm_num [world12733, agent12733, scalar12733, tp12733, tm12733, ep12733, em12733, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12733, agent12733, tp12733, tm12733, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12733, agent12733, tp12733, tm12733, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12733, agent12733, scalar12733, tp12733, tm12733, ep12733, em12733, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12733, agent12733, tp12733, tm12733, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12733, agent12733, scalar12733, tp12733, tm12733, ep12733, em12733, dsL]

theorem tails12733 :
    exp (-((12733:ℝ)*ep12733)) ≤ scalar12733.upperTail ∧
    exp (-((12733:ℝ)*em12733)) ≤ scalar12733.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12733:ℝ)) (by norm_num [ep12733]) ?_)
      (show bp12733^8 ≤ scalar12733.upperTail by norm_num [bp12733, scalar12733])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12733, bp12733, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12733:ℝ)) (by norm_num [em12733]) ?_)
      (show bm12733^8 ≤ scalar12733.lowerTail by norm_num [bm12733, scalar12733])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12733, bm12733, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12733 :
    agent12733.root+dsL+scalar12733.worldRadius < √(1/100/aL) ∧
    2*(agent12733.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12733, agent12733, scalar12733, tp12733, tm12733, ep12733, em12733, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12733, agent12733, scalar12733, tp12733, tm12733, ep12733, em12733, dsL]

noncomputable def master12733 : MasterCertificate 12733 world12733 agent12733 :=
  master scalar12733 dsL tp12733 tm12733 ep12733 em12733
    (by norm_num [dsL]) (by norm_num [tp12733]) (by norm_num [tm12733])
    (by norm_num [ep12733]) (by norm_num [em12733])
    positive12733 negative12733 tails12733.1 tails12733.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12733.1 tailGuards12733.2

theorem preserves12733 : master12733.toScalarCertificate = scalar12733 := rfl

noncomputable def tp12734 : ℝ := (2319597031 / 10000000000)
noncomputable def tm12734 : ℝ := (-((758720369 / 1250000000)))
noncomputable def ep12734 : ℝ := (51517550228693723 / 100000000000000000000)
noncomputable def em12734 : ℝ := (25095142583506109 / 50000000000000000000)
noncomputable def bp12734 : ℝ := (44041817496445745683 / 100000000000000000000)
noncomputable def bm12734 : ℝ := (44982175974120282327 / 100000000000000000000)

theorem positive12734 :
    Eplus aL (agent12734.root+dsL) scalar12734.worldRadius world12734.frame
      agent12734.frame tp12734 ≤ -ep12734 := by
  apply positive_check (eT := (14450658000727362959 / 12500000000000000000)) (y := (2367872731347936563 / 6250000000000000000)) (u := (146061800465228120497 / 100000000000000000000))
  · norm_num [world12734, agent12734, scalar12734, tp12734, tm12734, ep12734, em12734, dsL]
  · norm_num [world12734, agent12734, scalar12734, tp12734, tm12734, ep12734, em12734, dsL]
  · norm_num [world12734, agent12734, scalar12734, tp12734, tm12734, ep12734, em12734, dsL]
  · norm_num [world12734, agent12734, scalar12734, tp12734, tm12734, ep12734, em12734, dsL]
  · norm_num [world12734, agent12734, scalar12734, tp12734, tm12734, ep12734, em12734, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12734, agent12734, tp12734, tm12734, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12734, agent12734, scalar12734, tp12734, tm12734, ep12734, em12734, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12734, agent12734, tp12734, tm12734, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12734, agent12734, scalar12734, tp12734, tm12734, ep12734, em12734, dsL]

theorem negative12734 :
    Eminus aL (agent12734.root+dsL) scalar12734.worldRadius world12734.frame
      agent12734.frame tm12734 ≤ -em12734 := by
  apply negative_check (lo := (34211687770415843913 / 50000000000000000000)) (hi := (68423375540831687827 / 100000000000000000000))
    (y := (-((35842078961659588651 / 50000000000000000000)))) (u := (48829205477973356383 / 100000000000000000000))
  · norm_num [world12734, agent12734, scalar12734, tp12734, tm12734, ep12734, em12734, dsL]
  · norm_num [world12734, agent12734, scalar12734, tp12734, tm12734, ep12734, em12734, dsL]
  · norm_num [world12734, agent12734, scalar12734, tp12734, tm12734, ep12734, em12734, dsL]
  · norm_num [world12734, agent12734, scalar12734, tp12734, tm12734, ep12734, em12734, dsL]
  · norm_num [world12734, agent12734, scalar12734, tp12734, tm12734, ep12734, em12734, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12734, agent12734, tp12734, tm12734, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12734, agent12734, tp12734, tm12734, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12734, agent12734, scalar12734, tp12734, tm12734, ep12734, em12734, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12734, agent12734, tp12734, tm12734, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12734, agent12734, scalar12734, tp12734, tm12734, ep12734, em12734, dsL]

theorem tails12734 :
    exp (-((12734:ℝ)*ep12734)) ≤ scalar12734.upperTail ∧
    exp (-((12734:ℝ)*em12734)) ≤ scalar12734.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12734:ℝ)) (by norm_num [ep12734]) ?_)
      (show bp12734^8 ≤ scalar12734.upperTail by norm_num [bp12734, scalar12734])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12734, bp12734, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12734:ℝ)) (by norm_num [em12734]) ?_)
      (show bm12734^8 ≤ scalar12734.lowerTail by norm_num [bm12734, scalar12734])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12734, bm12734, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12734 :
    agent12734.root+dsL+scalar12734.worldRadius < √(1/100/aL) ∧
    2*(agent12734.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12734, agent12734, scalar12734, tp12734, tm12734, ep12734, em12734, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12734, agent12734, scalar12734, tp12734, tm12734, ep12734, em12734, dsL]

noncomputable def master12734 : MasterCertificate 12734 world12734 agent12734 :=
  master scalar12734 dsL tp12734 tm12734 ep12734 em12734
    (by norm_num [dsL]) (by norm_num [tp12734]) (by norm_num [tm12734])
    (by norm_num [ep12734]) (by norm_num [em12734])
    positive12734 negative12734 tails12734.1 tails12734.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12734.1 tailGuards12734.2

theorem preserves12734 : master12734.toScalarCertificate = scalar12734 := rfl

noncomputable def tp12735 : ℝ := (463936179 / 2000000000)
noncomputable def tm12735 : ℝ := (-((758742831 / 1250000000)))
noncomputable def ep12735 : ℝ := (25760063480520691 / 50000000000000000000)
noncomputable def em12735 : ℝ := (10038498541698723 / 20000000000000000000)
noncomputable def bp12735 : ℝ := (22018587529960504017 / 50000000000000000000)
noncomputable def bm12735 : ℝ := (44977773372102211119 / 100000000000000000000)

theorem positive12735 :
    Eplus aL (agent12735.root+dsL) scalar12735.worldRadius world12735.frame
      agent12735.frame tp12735 ≤ -ep12735 := by
  apply positive_check (eT := (1806335951840759503 / 1562500000000000000)) (y := (37886745865296609973 / 100000000000000000000)) (u := (146062942912122093493 / 100000000000000000000))
  · norm_num [world12735, agent12735, scalar12735, tp12735, tm12735, ep12735, em12735, dsL]
  · norm_num [world12735, agent12735, scalar12735, tp12735, tm12735, ep12735, em12735, dsL]
  · norm_num [world12735, agent12735, scalar12735, tp12735, tm12735, ep12735, em12735, dsL]
  · norm_num [world12735, agent12735, scalar12735, tp12735, tm12735, ep12735, em12735, dsL]
  · norm_num [world12735, agent12735, scalar12735, tp12735, tm12735, ep12735, em12735, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12735, agent12735, tp12735, tm12735, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12735, agent12735, scalar12735, tp12735, tm12735, ep12735, em12735, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12735, agent12735, tp12735, tm12735, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12735, agent12735, scalar12735, tp12735, tm12735, ep12735, em12735, dsL]

theorem negative12735 :
    Eminus aL (agent12735.root+dsL) scalar12735.worldRadius world12735.frame
      agent12735.frame tm12735 ≤ -em12735 := by
  apply negative_check (lo := (68423178663722543827 / 100000000000000000000)) (hi := (17105794665930635957 / 25000000000000000000))
    (y := (-((1792105533725459591 / 2500000000000000000)))) (u := (4882917450771818663 / 10000000000000000000))
  · norm_num [world12735, agent12735, scalar12735, tp12735, tm12735, ep12735, em12735, dsL]
  · norm_num [world12735, agent12735, scalar12735, tp12735, tm12735, ep12735, em12735, dsL]
  · norm_num [world12735, agent12735, scalar12735, tp12735, tm12735, ep12735, em12735, dsL]
  · norm_num [world12735, agent12735, scalar12735, tp12735, tm12735, ep12735, em12735, dsL]
  · norm_num [world12735, agent12735, scalar12735, tp12735, tm12735, ep12735, em12735, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12735, agent12735, tp12735, tm12735, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12735, agent12735, tp12735, tm12735, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12735, agent12735, scalar12735, tp12735, tm12735, ep12735, em12735, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12735, agent12735, tp12735, tm12735, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12735, agent12735, scalar12735, tp12735, tm12735, ep12735, em12735, dsL]

theorem tails12735 :
    exp (-((12735:ℝ)*ep12735)) ≤ scalar12735.upperTail ∧
    exp (-((12735:ℝ)*em12735)) ≤ scalar12735.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12735:ℝ)) (by norm_num [ep12735]) ?_)
      (show bp12735^8 ≤ scalar12735.upperTail by norm_num [bp12735, scalar12735])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12735, bp12735, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12735:ℝ)) (by norm_num [em12735]) ?_)
      (show bm12735^8 ≤ scalar12735.lowerTail by norm_num [bm12735, scalar12735])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12735, bm12735, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12735 :
    agent12735.root+dsL+scalar12735.worldRadius < √(1/100/aL) ∧
    2*(agent12735.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12735, agent12735, scalar12735, tp12735, tm12735, ep12735, em12735, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12735, agent12735, scalar12735, tp12735, tm12735, ep12735, em12735, dsL]

noncomputable def master12735 : MasterCertificate 12735 world12735 agent12735 :=
  master scalar12735 dsL tp12735 tm12735 ep12735 em12735
    (by norm_num [dsL]) (by norm_num [tp12735]) (by norm_num [tm12735])
    (by norm_num [ep12735]) (by norm_num [em12735])
    positive12735 negative12735 tails12735.1 tails12735.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12735.1 tailGuards12735.2

theorem preserves12735 : master12735.toScalarCertificate = scalar12735 := rfl

noncomputable def tp12736 : ℝ := (231976477 / 1000000000)
noncomputable def tm12736 : ℝ := (-((6070122181 / 10000000000)))
noncomputable def ep12736 : ℝ := (25761351385542071 / 50000000000000000000)
noncomputable def em12736 : ℝ := (501946993821149 / 1000000000000000000)
noncomputable def bp12736 : ℝ := (44032533475637989567 / 100000000000000000000)
noncomputable def bm12736 : ℝ := (8994674314830328919 / 20000000000000000000)

theorem positive12736 :
    Eplus aL (agent12736.root+dsL) scalar12736.worldRadius world12736.frame
      agent12736.frame tp12736 ≤ -ep12736 := by
  apply positive_check (eT := (14450717242763829311 / 12500000000000000000)) (y := (18943764267415817881 / 50000000000000000000)) (u := (73032043053375970497 / 50000000000000000000))
  · norm_num [world12736, agent12736, scalar12736, tp12736, tm12736, ep12736, em12736, dsL]
  · norm_num [world12736, agent12736, scalar12736, tp12736, tm12736, ep12736, em12736, dsL]
  · norm_num [world12736, agent12736, scalar12736, tp12736, tm12736, ep12736, em12736, dsL]
  · norm_num [world12736, agent12736, scalar12736, tp12736, tm12736, ep12736, em12736, dsL]
  · norm_num [world12736, agent12736, scalar12736, tp12736, tm12736, ep12736, em12736, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12736, agent12736, tp12736, tm12736, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12736, agent12736, scalar12736, tp12736, tm12736, ep12736, em12736, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12736, agent12736, tp12736, tm12736, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12736, agent12736, scalar12736, tp12736, tm12736, ep12736, em12736, dsL]

theorem negative12736 :
    Eminus aL (agent12736.root+dsL) scalar12736.worldRadius world12736.frame
      agent12736.frame tm12736 ≤ -em12736 := by
  apply negative_check (lo := (34211491213411148137 / 50000000000000000000)) (hi := (2736919297072891851 / 4000000000000000000))
    (y := (-((71684283745449007297 / 100000000000000000000)))) (u := (24414572020032848091 / 50000000000000000000))
  · norm_num [world12736, agent12736, scalar12736, tp12736, tm12736, ep12736, em12736, dsL]
  · norm_num [world12736, agent12736, scalar12736, tp12736, tm12736, ep12736, em12736, dsL]
  · norm_num [world12736, agent12736, scalar12736, tp12736, tm12736, ep12736, em12736, dsL]
  · norm_num [world12736, agent12736, scalar12736, tp12736, tm12736, ep12736, em12736, dsL]
  · norm_num [world12736, agent12736, scalar12736, tp12736, tm12736, ep12736, em12736, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12736, agent12736, tp12736, tm12736, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12736, agent12736, tp12736, tm12736, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12736, agent12736, scalar12736, tp12736, tm12736, ep12736, em12736, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12736, agent12736, tp12736, tm12736, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12736, agent12736, scalar12736, tp12736, tm12736, ep12736, em12736, dsL]

theorem tails12736 :
    exp (-((12736:ℝ)*ep12736)) ≤ scalar12736.upperTail ∧
    exp (-((12736:ℝ)*em12736)) ≤ scalar12736.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12736:ℝ)) (by norm_num [ep12736]) ?_)
      (show bp12736^8 ≤ scalar12736.upperTail by norm_num [bp12736, scalar12736])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12736, bp12736, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12736:ℝ)) (by norm_num [em12736]) ?_)
      (show bm12736^8 ≤ scalar12736.lowerTail by norm_num [bm12736, scalar12736])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12736, bm12736, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12736 :
    agent12736.root+dsL+scalar12736.worldRadius < √(1/100/aL) ∧
    2*(agent12736.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12736, agent12736, scalar12736, tp12736, tm12736, ep12736, em12736, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12736, agent12736, scalar12736, tp12736, tm12736, ep12736, em12736, dsL]

noncomputable def master12736 : MasterCertificate 12736 world12736 agent12736 :=
  master scalar12736 dsL tp12736 tm12736 ep12736 em12736
    (by norm_num [dsL]) (by norm_num [tp12736]) (by norm_num [tm12736])
    (by norm_num [ep12736]) (by norm_num [em12736])
    positive12736 negative12736 tails12736.1 tails12736.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12736.1 tailGuards12736.2

theorem preserves12736 : master12736.toScalarCertificate = scalar12736 := rfl

noncomputable def tp12737 : ℝ := (2319848581 / 10000000000)
noncomputable def tm12737 : ℝ := (-((1214060329 / 2000000000)))
noncomputable def ep12737 : ℝ := (2576263845029341 / 5000000000000000000)
noncomputable def em12737 : ℝ := (50196904514193233 / 100000000000000000000)
noncomputable def bp12737 : ℝ := (1100697331877241207 / 2500000000000000000)
noncomputable def bm12737 : ℝ := (44968971062594664367 / 100000000000000000000)

theorem positive12737 :
    Eplus aL (agent12737.root+dsL) scalar12737.worldRadius world12737.frame
      agent12737.frame tp12737 ≤ -ep12737 := by
  apply positive_check (eT := (57802987268361609567 / 50000000000000000000)) (y := (37888310544029674509 / 100000000000000000000)) (u := (146065228345806528443 / 100000000000000000000))
  · norm_num [world12737, agent12737, scalar12737, tp12737, tm12737, ep12737, em12737, dsL]
  · norm_num [world12737, agent12737, scalar12737, tp12737, tm12737, ep12737, em12737, dsL]
  · norm_num [world12737, agent12737, scalar12737, tp12737, tm12737, ep12737, em12737, dsL]
  · norm_num [world12737, agent12737, scalar12737, tp12737, tm12737, ep12737, em12737, dsL]
  · norm_num [world12737, agent12737, scalar12737, tp12737, tm12737, ep12737, em12737, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12737, agent12737, tp12737, tm12737, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12737, agent12737, scalar12737, tp12737, tm12737, ep12737, em12737, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12737, agent12737, tp12737, tm12737, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12737, agent12737, scalar12737, tp12737, tm12737, ep12737, em12737, dsL]

theorem negative12737 :
    Eminus aL (agent12737.root+dsL) scalar12737.worldRadius world12737.frame
      agent12737.frame tm12737 ≤ -em12737 := by
  apply negative_check (lo := (13684557285602555903 / 20000000000000000000)) (hi := (17105696607003194879 / 25000000000000000000))
    (y := (-((71684346305954155631 / 100000000000000000000)))) (u := (12207278373079020131 / 25000000000000000000))
  · norm_num [world12737, agent12737, scalar12737, tp12737, tm12737, ep12737, em12737, dsL]
  · norm_num [world12737, agent12737, scalar12737, tp12737, tm12737, ep12737, em12737, dsL]
  · norm_num [world12737, agent12737, scalar12737, tp12737, tm12737, ep12737, em12737, dsL]
  · norm_num [world12737, agent12737, scalar12737, tp12737, tm12737, ep12737, em12737, dsL]
  · norm_num [world12737, agent12737, scalar12737, tp12737, tm12737, ep12737, em12737, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12737, agent12737, tp12737, tm12737, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12737, agent12737, tp12737, tm12737, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12737, agent12737, scalar12737, tp12737, tm12737, ep12737, em12737, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12737, agent12737, tp12737, tm12737, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12737, agent12737, scalar12737, tp12737, tm12737, ep12737, em12737, dsL]

theorem tails12737 :
    exp (-((12737:ℝ)*ep12737)) ≤ scalar12737.upperTail ∧
    exp (-((12737:ℝ)*em12737)) ≤ scalar12737.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12737:ℝ)) (by norm_num [ep12737]) ?_)
      (show bp12737^8 ≤ scalar12737.upperTail by norm_num [bp12737, scalar12737])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12737, bp12737, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12737:ℝ)) (by norm_num [em12737]) ?_)
      (show bm12737^8 ≤ scalar12737.lowerTail by norm_num [bm12737, scalar12737])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12737, bm12737, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12737 :
    agent12737.root+dsL+scalar12737.worldRadius < √(1/100/aL) ∧
    2*(agent12737.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12737, agent12737, scalar12737, tp12737, tm12737, ep12737, em12737, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12737, agent12737, scalar12737, tp12737, tm12737, ep12737, em12737, dsL]

noncomputable def master12737 : MasterCertificate 12737 world12737 agent12737 :=
  master scalar12737 dsL tp12737 tm12737 ep12737 em12737
    (by norm_num [dsL]) (by norm_num [tp12737]) (by norm_num [tm12737])
    (by norm_num [ep12737]) (by norm_num [em12737])
    positive12737 negative12737 tails12737.1 tails12737.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12737.1 tailGuards12737.2

theorem preserves12737 : master12737.toScalarCertificate = scalar12737 := rfl

noncomputable def tp12738 : ℝ := (579983103 / 2500000000)
noncomputable def tm12738 : ℝ := (-((379405061 / 625000000)))
noncomputable def ep12738 : ℝ := (2061113973284231 / 4000000000000000000)
noncomputable def em12738 : ℝ := (50199108082730163 / 100000000000000000000)
noncomputable def bp12738 : ℝ := (22011627235223180827 / 50000000000000000000)
noncomputable def bm12738 : ℝ := (44964571853147641469 / 100000000000000000000)

theorem positive12738 :
    Eplus aL (agent12738.root+dsL) scalar12738.worldRadius world12738.frame
      agent12738.frame tp12738 ≤ -ep12738 := by
  apply positive_check (eT := (115606211308712581303 / 100000000000000000000)) (y := (18944546632341137509 / 50000000000000000000)) (u := (146066371632989425777 / 100000000000000000000))
  · norm_num [world12738, agent12738, scalar12738, tp12738, tm12738, ep12738, em12738, dsL]
  · norm_num [world12738, agent12738, scalar12738, tp12738, tm12738, ep12738, em12738, dsL]
  · norm_num [world12738, agent12738, scalar12738, tp12738, tm12738, ep12738, em12738, dsL]
  · norm_num [world12738, agent12738, scalar12738, tp12738, tm12738, ep12738, em12738, dsL]
  · norm_num [world12738, agent12738, scalar12738, tp12738, tm12738, ep12738, em12738, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12738, agent12738, tp12738, tm12738, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12738, agent12738, scalar12738, tp12738, tm12738, ep12738, em12738, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12738, agent12738, tp12738, tm12738, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12738, agent12738, scalar12738, tp12738, tm12738, ep12738, em12738, dsL]

theorem negative12738 :
    Eminus aL (agent12738.root+dsL) scalar12738.worldRadius world12738.frame
      agent12738.frame tm12738 ≤ -em12738 := by
  apply negative_check (lo := (68422590940999494261 / 100000000000000000000)) (hi := (34211295470499747131 / 50000000000000000000))
    (y := (-((71684407996686271753 / 100000000000000000000)))) (u := (48829083369287772861 / 100000000000000000000))
  · norm_num [world12738, agent12738, scalar12738, tp12738, tm12738, ep12738, em12738, dsL]
  · norm_num [world12738, agent12738, scalar12738, tp12738, tm12738, ep12738, em12738, dsL]
  · norm_num [world12738, agent12738, scalar12738, tp12738, tm12738, ep12738, em12738, dsL]
  · norm_num [world12738, agent12738, scalar12738, tp12738, tm12738, ep12738, em12738, dsL]
  · norm_num [world12738, agent12738, scalar12738, tp12738, tm12738, ep12738, em12738, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12738, agent12738, tp12738, tm12738, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12738, agent12738, tp12738, tm12738, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12738, agent12738, scalar12738, tp12738, tm12738, ep12738, em12738, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12738, agent12738, tp12738, tm12738, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12738, agent12738, scalar12738, tp12738, tm12738, ep12738, em12738, dsL]

theorem tails12738 :
    exp (-((12738:ℝ)*ep12738)) ≤ scalar12738.upperTail ∧
    exp (-((12738:ℝ)*em12738)) ≤ scalar12738.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12738:ℝ)) (by norm_num [ep12738]) ?_)
      (show bp12738^8 ≤ scalar12738.upperTail by norm_num [bp12738, scalar12738])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12738, bp12738, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12738:ℝ)) (by norm_num [em12738]) ?_)
      (show bm12738^8 ≤ scalar12738.lowerTail by norm_num [bm12738, scalar12738])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12738, bm12738, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12738 :
    agent12738.root+dsL+scalar12738.worldRadius < √(1/100/aL) ∧
    2*(agent12738.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12738, agent12738, scalar12738, tp12738, tm12738, ep12738, em12738, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12738, agent12738, scalar12738, tp12738, tm12738, ep12738, em12738, dsL]

noncomputable def master12738 : MasterCertificate 12738 world12738 agent12738 :=
  master scalar12738 dsL tp12738 tm12738 ep12738 em12738
    (by norm_num [dsL]) (by norm_num [tp12738]) (by norm_num [tm12738])
    (by norm_num [ep12738]) (by norm_num [em12738])
    positive12738 negative12738 tails12738.1 tails12738.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12738.1 tailGuards12738.2

theorem preserves12738 : master12738.toScalarCertificate = scalar12738 := rfl

noncomputable def tp12739 : ℝ := (2320016413 / 10000000000)
noncomputable def tm12739 : ℝ := (-((189708163 / 312500000)))
noncomputable def ep12739 : ℝ := (51530426083349011 / 100000000000000000000)
noncomputable def em12739 : ℝ := (25100658243761119 / 50000000000000000000)
noncomputable def bp12739 : ℝ := (22009306421794716641 / 50000000000000000000)
noncomputable def bm12739 : ℝ := (22480084681970461923 / 50000000000000000000)

theorem positive12739 :
    Eplus aL (agent12739.root+dsL) scalar12739.worldRadius world12739.frame
      agent12739.frame tp12739 ≤ -ep12739 := by
  apply positive_check (eT := (57803224670993476659 / 50000000000000000000)) (y := (18944935994283048557 / 50000000000000000000)) (u := (29213501818228077521 / 20000000000000000000))
  · norm_num [world12739, agent12739, scalar12739, tp12739, tm12739, ep12739, em12739, dsL]
  · norm_num [world12739, agent12739, scalar12739, tp12739, tm12739, ep12739, em12739, dsL]
  · norm_num [world12739, agent12739, scalar12739, tp12739, tm12739, ep12739, em12739, dsL]
  · norm_num [world12739, agent12739, scalar12739, tp12739, tm12739, ep12739, em12739, dsL]
  · norm_num [world12739, agent12739, scalar12739, tp12739, tm12739, ep12739, em12739, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12739, agent12739, tp12739, tm12739, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12739, agent12739, scalar12739, tp12739, tm12739, ep12739, em12739, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12739, agent12739, tp12739, tm12739, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12739, agent12739, scalar12739, tp12739, tm12739, ep12739, em12739, dsL]

theorem negative12739 :
    Eminus aL (agent12739.root+dsL) scalar12739.worldRadius world12739.frame
      agent12739.frame tm12739 ≤ -em12739 := by
  apply negative_check (lo := (68422391509176071863 / 100000000000000000000)) (hi := (8552798938647008983 / 12500000000000000000))
    (y := (-((71684464606653145733 / 100000000000000000000)))) (u := (48829055727167676737 / 100000000000000000000))
  · norm_num [world12739, agent12739, scalar12739, tp12739, tm12739, ep12739, em12739, dsL]
  · norm_num [world12739, agent12739, scalar12739, tp12739, tm12739, ep12739, em12739, dsL]
  · norm_num [world12739, agent12739, scalar12739, tp12739, tm12739, ep12739, em12739, dsL]
  · norm_num [world12739, agent12739, scalar12739, tp12739, tm12739, ep12739, em12739, dsL]
  · norm_num [world12739, agent12739, scalar12739, tp12739, tm12739, ep12739, em12739, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12739, agent12739, tp12739, tm12739, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12739, agent12739, tp12739, tm12739, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12739, agent12739, scalar12739, tp12739, tm12739, ep12739, em12739, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12739, agent12739, tp12739, tm12739, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12739, agent12739, scalar12739, tp12739, tm12739, ep12739, em12739, dsL]

theorem tails12739 :
    exp (-((12739:ℝ)*ep12739)) ≤ scalar12739.upperTail ∧
    exp (-((12739:ℝ)*em12739)) ≤ scalar12739.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12739:ℝ)) (by norm_num [ep12739]) ?_)
      (show bp12739^8 ≤ scalar12739.upperTail by norm_num [bp12739, scalar12739])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12739, bp12739, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12739:ℝ)) (by norm_num [em12739]) ?_)
      (show bm12739^8 ≤ scalar12739.lowerTail by norm_num [bm12739, scalar12739])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12739, bm12739, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12739 :
    agent12739.root+dsL+scalar12739.worldRadius < √(1/100/aL) ∧
    2*(agent12739.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12739, agent12739, scalar12739, tp12739, tm12739, ep12739, em12739, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12739, agent12739, scalar12739, tp12739, tm12739, ep12739, em12739, dsL]

noncomputable def master12739 : MasterCertificate 12739 world12739 agent12739 :=
  master scalar12739 dsL tp12739 tm12739 ep12739 em12739
    (by norm_num [dsL]) (by norm_num [tp12739]) (by norm_num [tm12739])
    (by norm_num [ep12739]) (by norm_num [em12739])
    positive12739 negative12739 tails12739.1 tails12739.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12739.1 tailGuards12739.2

theorem preserves12739 : master12739.toScalarCertificate = scalar12739 := rfl

noncomputable def tp12740 : ℝ := (2320174493 / 10000000000)
noncomputable def tm12740 : ℝ := (-((6071065071 / 10000000000)))
noncomputable def ep12740 : ℝ := (2061376614629327 / 4000000000000000000)
noncomputable def em12740 : ℝ := (50205064144860523 / 100000000000000000000)
noncomputable def bp12740 : ℝ := (5501622669859702509 / 12500000000000000000)
noncomputable def bm12740 : ℝ := (44954665088495848341 / 100000000000000000000)

theorem positive12740 :
    Eplus aL (agent12740.root+dsL) scalar12740.worldRadius world12740.frame
      agent12740.frame tp12740 ≤ -ep12740 := by
  apply positive_check (eT := (2312144454500047771 / 2000000000000000000)) (y := (37889927346656771537 / 100000000000000000000)) (u := (146067589951346897481 / 100000000000000000000))
  · norm_num [world12740, agent12740, scalar12740, tp12740, tm12740, ep12740, em12740, dsL]
  · norm_num [world12740, agent12740, scalar12740, tp12740, tm12740, ep12740, em12740, dsL]
  · norm_num [world12740, agent12740, scalar12740, tp12740, tm12740, ep12740, em12740, dsL]
  · norm_num [world12740, agent12740, scalar12740, tp12740, tm12740, ep12740, em12740, dsL]
  · norm_num [world12740, agent12740, scalar12740, tp12740, tm12740, ep12740, em12740, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12740, agent12740, tp12740, tm12740, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12740, agent12740, scalar12740, tp12740, tm12740, ep12740, em12740, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12740, agent12740, tp12740, tm12740, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12740, agent12740, scalar12740, tp12740, tm12740, ep12740, em12740, dsL]

theorem negative12740 :
    Eminus aL (agent12740.root+dsL) scalar12740.worldRadius world12740.frame
      agent12740.frame tm12740 ≤ -em12740 := by
  apply negative_check (lo := (68421235648564856991 / 100000000000000000000)) (hi := (2138163614017651781 / 3125000000000000000))
    (y := (-((28001021630415139 / 39062500000000000)))) (u := (24414979349213207923 / 50000000000000000000))
  · norm_num [world12740, agent12740, scalar12740, tp12740, tm12740, ep12740, em12740, dsL]
  · norm_num [world12740, agent12740, scalar12740, tp12740, tm12740, ep12740, em12740, dsL]
  · norm_num [world12740, agent12740, scalar12740, tp12740, tm12740, ep12740, em12740, dsL]
  · norm_num [world12740, agent12740, scalar12740, tp12740, tm12740, ep12740, em12740, dsL]
  · norm_num [world12740, agent12740, scalar12740, tp12740, tm12740, ep12740, em12740, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12740, agent12740, tp12740, tm12740, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12740, agent12740, tp12740, tm12740, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12740, agent12740, scalar12740, tp12740, tm12740, ep12740, em12740, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12740, agent12740, tp12740, tm12740, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12740, agent12740, scalar12740, tp12740, tm12740, ep12740, em12740, dsL]

theorem tails12740 :
    exp (-((12740:ℝ)*ep12740)) ≤ scalar12740.upperTail ∧
    exp (-((12740:ℝ)*em12740)) ≤ scalar12740.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12740:ℝ)) (by norm_num [ep12740]) ?_)
      (show bp12740^8 ≤ scalar12740.upperTail by norm_num [bp12740, scalar12740])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12740, bp12740, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12740:ℝ)) (by norm_num [em12740]) ?_)
      (show bm12740^8 ≤ scalar12740.lowerTail by norm_num [bm12740, scalar12740])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12740, bm12740, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12740 :
    agent12740.root+dsL+scalar12740.worldRadius < √(1/100/aL) ∧
    2*(agent12740.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12740, agent12740, scalar12740, tp12740, tm12740, ep12740, em12740, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12740, agent12740, scalar12740, tp12740, tm12740, ep12740, em12740, dsL]

noncomputable def master12740 : MasterCertificate 12740 world12740 agent12740 :=
  master scalar12740 dsL tp12740 tm12740 ep12740 em12740
    (by norm_num [dsL]) (by norm_num [tp12740]) (by norm_num [tm12740])
    (by norm_num [ep12740]) (by norm_num [em12740])
    positive12740 negative12740 tails12740.1 tails12740.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12740.1 tailGuards12740.2

theorem preserves12740 : master12740.toScalarCertificate = scalar12740 := rfl

noncomputable def tp12741 : ℝ := (2320258471 / 10000000000)
noncomputable def tm12741 : ℝ := (-((6071245087 / 10000000000)))
noncomputable def ep12741 : ℝ := (25768494998821363 / 50000000000000000000)
noncomputable def em12741 : ℝ := (25103635346688223 / 50000000000000000000)
noncomputable def bp12741 : ℝ := (4400834165589292047 / 10000000000000000000)
noncomputable def bm12741 : ℝ := (22475132157660501783 / 50000000000000000000)

theorem positive12741 :
    Eplus aL (agent12741.root+dsL) scalar12741.worldRadius world12741.frame
      agent12741.frame tp12741 ≤ -ep12741 := by
  apply positive_check (eT := (14450932580863165607 / 12500000000000000000)) (y := (37890705498041858881 / 100000000000000000000)) (u := (36517181645685904583 / 25000000000000000000))
  · norm_num [world12741, agent12741, scalar12741, tp12741, tm12741, ep12741, em12741, dsL]
  · norm_num [world12741, agent12741, scalar12741, tp12741, tm12741, ep12741, em12741, dsL]
  · norm_num [world12741, agent12741, scalar12741, tp12741, tm12741, ep12741, em12741, dsL]
  · norm_num [world12741, agent12741, scalar12741, tp12741, tm12741, ep12741, em12741, dsL]
  · norm_num [world12741, agent12741, scalar12741, tp12741, tm12741, ep12741, em12741, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12741, agent12741, tp12741, tm12741, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12741, agent12741, scalar12741, tp12741, tm12741, ep12741, em12741, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12741, agent12741, tp12741, tm12741, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12741, agent12741, scalar12741, tp12741, tm12741, ep12741, em12741, dsL]

theorem negative12741 :
    Eminus aL (agent12741.root+dsL) scalar12741.worldRadius world12741.frame
      agent12741.frame tm12741 ≤ -em12741 := by
  apply negative_check (lo := (68421037084901221483 / 100000000000000000000)) (hi := (17105259271225305371 / 25000000000000000000))
    (y := (-((4480166827216421357 / 6250000000000000000)))) (u := (48829932397836471393 / 100000000000000000000))
  · norm_num [world12741, agent12741, scalar12741, tp12741, tm12741, ep12741, em12741, dsL]
  · norm_num [world12741, agent12741, scalar12741, tp12741, tm12741, ep12741, em12741, dsL]
  · norm_num [world12741, agent12741, scalar12741, tp12741, tm12741, ep12741, em12741, dsL]
  · norm_num [world12741, agent12741, scalar12741, tp12741, tm12741, ep12741, em12741, dsL]
  · norm_num [world12741, agent12741, scalar12741, tp12741, tm12741, ep12741, em12741, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12741, agent12741, tp12741, tm12741, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12741, agent12741, tp12741, tm12741, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12741, agent12741, scalar12741, tp12741, tm12741, ep12741, em12741, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12741, agent12741, tp12741, tm12741, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12741, agent12741, scalar12741, tp12741, tm12741, ep12741, em12741, dsL]

theorem tails12741 :
    exp (-((12741:ℝ)*ep12741)) ≤ scalar12741.upperTail ∧
    exp (-((12741:ℝ)*em12741)) ≤ scalar12741.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12741:ℝ)) (by norm_num [ep12741]) ?_)
      (show bp12741^8 ≤ scalar12741.upperTail by norm_num [bp12741, scalar12741])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12741, bp12741, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12741:ℝ)) (by norm_num [em12741]) ?_)
      (show bm12741^8 ≤ scalar12741.lowerTail by norm_num [bm12741, scalar12741])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12741, bm12741, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12741 :
    agent12741.root+dsL+scalar12741.worldRadius < √(1/100/aL) ∧
    2*(agent12741.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12741, agent12741, scalar12741, tp12741, tm12741, ep12741, em12741, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12741, agent12741, scalar12741, tp12741, tm12741, ep12741, em12741, dsL]

noncomputable def master12741 : MasterCertificate 12741 world12741 agent12741 :=
  master scalar12741 dsL tp12741 tm12741 ep12741 em12741
    (by norm_num [dsL]) (by norm_num [tp12741]) (by norm_num [tm12741])
    (by norm_num [ep12741]) (by norm_num [em12741])
    positive12741 negative12741 tails12741.1 tails12741.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12741.1 tailGuards12741.2

theorem preserves12741 : master12741.toScalarCertificate = scalar12741 := rfl

noncomputable def tp12742 : ℝ := (580085597 / 2500000000)
noncomputable def tm12742 : ℝ := (-((6071425089 / 10000000000)))
noncomputable def ep12742 : ℝ := (51539562652332459 / 100000000000000000000)
noncomputable def em12742 : ℝ := (50209475385833553 / 100000000000000000000)
noncomputable def bp12742 : ℝ := (22001851772274530797 / 50000000000000000000)
noncomputable def bm12742 : ℝ := (44945865053722112037 / 100000000000000000000)

theorem positive12742 :
    Eplus aL (agent12742.root+dsL) scalar12742.worldRadius world12742.frame
      agent12742.frame tp12742 ≤ -ep12742 := by
  apply positive_check (eT := (57803849080382861743 / 50000000000000000000)) (y := (7578296648499639501 / 20000000000000000000)) (u := (36517465657146205273 / 25000000000000000000))
  · norm_num [world12742, agent12742, scalar12742, tp12742, tm12742, ep12742, em12742, dsL]
  · norm_num [world12742, agent12742, scalar12742, tp12742, tm12742, ep12742, em12742, dsL]
  · norm_num [world12742, agent12742, scalar12742, tp12742, tm12742, ep12742, em12742, dsL]
  · norm_num [world12742, agent12742, scalar12742, tp12742, tm12742, ep12742, em12742, dsL]
  · norm_num [world12742, agent12742, scalar12742, tp12742, tm12742, ep12742, em12742, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12742, agent12742, tp12742, tm12742, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12742, agent12742, scalar12742, tp12742, tm12742, ep12742, em12742, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12742, agent12742, tp12742, tm12742, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12742, agent12742, scalar12742, tp12742, tm12742, ep12742, em12742, dsL]

theorem negative12742 :
    Eminus aL (agent12742.root+dsL) scalar12742.worldRadius world12742.frame
      agent12742.frame tm12742 ≤ -em12742 := by
  apply negative_check (lo := (68420838524259704249 / 100000000000000000000)) (hi := (273683354097038817 / 400000000000000000))
    (y := (-((71682723955627484347 / 100000000000000000000)))) (u := (48829905678024330143 / 100000000000000000000))
  · norm_num [world12742, agent12742, scalar12742, tp12742, tm12742, ep12742, em12742, dsL]
  · norm_num [world12742, agent12742, scalar12742, tp12742, tm12742, ep12742, em12742, dsL]
  · norm_num [world12742, agent12742, scalar12742, tp12742, tm12742, ep12742, em12742, dsL]
  · norm_num [world12742, agent12742, scalar12742, tp12742, tm12742, ep12742, em12742, dsL]
  · norm_num [world12742, agent12742, scalar12742, tp12742, tm12742, ep12742, em12742, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12742, agent12742, tp12742, tm12742, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12742, agent12742, tp12742, tm12742, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12742, agent12742, scalar12742, tp12742, tm12742, ep12742, em12742, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12742, agent12742, tp12742, tm12742, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12742, agent12742, scalar12742, tp12742, tm12742, ep12742, em12742, dsL]

theorem tails12742 :
    exp (-((12742:ℝ)*ep12742)) ≤ scalar12742.upperTail ∧
    exp (-((12742:ℝ)*em12742)) ≤ scalar12742.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12742:ℝ)) (by norm_num [ep12742]) ?_)
      (show bp12742^8 ≤ scalar12742.upperTail by norm_num [bp12742, scalar12742])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12742, bp12742, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12742:ℝ)) (by norm_num [em12742]) ?_)
      (show bm12742^8 ≤ scalar12742.lowerTail by norm_num [bm12742, scalar12742])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12742, bm12742, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12742 :
    agent12742.root+dsL+scalar12742.worldRadius < √(1/100/aL) ∧
    2*(agent12742.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12742, agent12742, scalar12742, tp12742, tm12742, ep12742, em12742, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12742, agent12742, scalar12742, tp12742, tm12742, ep12742, em12742, dsL]

noncomputable def master12742 : MasterCertificate 12742 world12742 agent12742 :=
  master scalar12742 dsL tp12742 tm12742 ep12742 em12742
    (by norm_num [dsL]) (by norm_num [tp12742]) (by norm_num [tm12742])
    (by norm_num [ep12742]) (by norm_num [em12742])
    positive12742 negative12742 tails12742.1 tails12742.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12742.1 tailGuards12742.2

theorem preserves12742 : master12742.toScalarCertificate = scalar12742 := rfl

noncomputable def tp12743 : ℝ := (2320426261 / 10000000000)
noncomputable def tm12743 : ℝ := (-((1214320969 / 2000000000)))
noncomputable def ep12743 : ℝ := (25771067431293047 / 50000000000000000000)
noncomputable def em12743 : ℝ := (10042335930526941 / 20000000000000000000)
noncomputable def bp12743 : ℝ := (43999065950520453273 / 100000000000000000000)
noncomputable def bm12743 : ℝ := (44941466279682300923 / 100000000000000000000)

theorem positive12743 :
    Eplus aL (agent12743.root+dsL) scalar12743.worldRadius world12743.frame
      agent12743.frame tp12743 ≤ -ep12743 := by
  apply positive_check (eT := (57803967694714872837 / 50000000000000000000)) (y := (37892260477413006199 / 100000000000000000000)) (u := (146070997938969192183 / 100000000000000000000))
  · norm_num [world12743, agent12743, scalar12743, tp12743, tm12743, ep12743, em12743, dsL]
  · norm_num [world12743, agent12743, scalar12743, tp12743, tm12743, ep12743, em12743, dsL]
  · norm_num [world12743, agent12743, scalar12743, tp12743, tm12743, ep12743, em12743, dsL]
  · norm_num [world12743, agent12743, scalar12743, tp12743, tm12743, ep12743, em12743, dsL]
  · norm_num [world12743, agent12743, scalar12743, tp12743, tm12743, ep12743, em12743, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12743, agent12743, tp12743, tm12743, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12743, agent12743, scalar12743, tp12743, tm12743, ep12743, em12743, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12743, agent12743, tp12743, tm12743, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12743, agent12743, scalar12743, tp12743, tm12743, ep12743, em12743, dsL]

theorem negative12743 :
    Eminus aL (agent12743.root+dsL) scalar12743.worldRadius world12743.frame
      agent12743.frame tm12743 ≤ -em12743 := by
  apply negative_check (lo := (13684128191764440807 / 20000000000000000000)) (hi := (17105160239705551009 / 25000000000000000000))
    (y := (-((71682776966865009929 / 100000000000000000000)))) (u := (9765975958538781743 / 20000000000000000000))
  · norm_num [world12743, agent12743, scalar12743, tp12743, tm12743, ep12743, em12743, dsL]
  · norm_num [world12743, agent12743, scalar12743, tp12743, tm12743, ep12743, em12743, dsL]
  · norm_num [world12743, agent12743, scalar12743, tp12743, tm12743, ep12743, em12743, dsL]
  · norm_num [world12743, agent12743, scalar12743, tp12743, tm12743, ep12743, em12743, dsL]
  · norm_num [world12743, agent12743, scalar12743, tp12743, tm12743, ep12743, em12743, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12743, agent12743, tp12743, tm12743, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12743, agent12743, tp12743, tm12743, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12743, agent12743, scalar12743, tp12743, tm12743, ep12743, em12743, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12743, agent12743, tp12743, tm12743, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12743, agent12743, scalar12743, tp12743, tm12743, ep12743, em12743, dsL]

theorem tails12743 :
    exp (-((12743:ℝ)*ep12743)) ≤ scalar12743.upperTail ∧
    exp (-((12743:ℝ)*em12743)) ≤ scalar12743.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12743:ℝ)) (by norm_num [ep12743]) ?_)
      (show bp12743^8 ≤ scalar12743.upperTail by norm_num [bp12743, scalar12743])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12743, bp12743, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12743:ℝ)) (by norm_num [em12743]) ?_)
      (show bm12743^8 ≤ scalar12743.lowerTail by norm_num [bm12743, scalar12743])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12743, bm12743, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12743 :
    agent12743.root+dsL+scalar12743.worldRadius < √(1/100/aL) ∧
    2*(agent12743.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12743, agent12743, scalar12743, tp12743, tm12743, ep12743, em12743, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12743, agent12743, scalar12743, tp12743, tm12743, ep12743, em12743, dsL]

noncomputable def master12743 : MasterCertificate 12743 world12743 agent12743 :=
  master scalar12743 dsL tp12743 tm12743 ep12743 em12743
    (by norm_num [dsL]) (by norm_num [tp12743]) (by norm_num [tm12743])
    (by norm_num [ep12743]) (by norm_num [em12743])
    positive12743 negative12743 tails12743.1 tails12743.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12743.1 tailGuards12743.2

theorem preserves12743 : master12743.toScalarCertificate = scalar12743 := rfl

noncomputable def tp12744 : ℝ := (2320510093 / 10000000000)
noncomputable def tm12744 : ℝ := (-((1517946153 / 2500000000)))
noncomputable def ep12744 : ℝ := (12886176349371273 / 25000000000000000000)
noncomputable def em12744 : ℝ := (50213882382633929 / 100000000000000000000)
noncomputable def bp12744 : ℝ := (10998607434121520007 / 25000000000000000000)
noncomputable def bm12744 : ℝ := (22468534394312745191 / 50000000000000000000)

theorem positive12744 :
    Eplus aL (agent12744.root+dsL) scalar12744.worldRadius world12744.frame
      agent12744.frame tp12744 ≤ -ep12744 := by
  apply positive_check (eT := (23121634470925410149 / 20000000000000000000)) (y := (37893037454237998593 / 100000000000000000000)) (u := (3651803322029508159 / 2500000000000000000))
  · norm_num [world12744, agent12744, scalar12744, tp12744, tm12744, ep12744, em12744, dsL]
  · norm_num [world12744, agent12744, scalar12744, tp12744, tm12744, ep12744, em12744, dsL]
  · norm_num [world12744, agent12744, scalar12744, tp12744, tm12744, ep12744, em12744, dsL]
  · norm_num [world12744, agent12744, scalar12744, tp12744, tm12744, ep12744, em12744, dsL]
  · norm_num [world12744, agent12744, scalar12744, tp12744, tm12744, ep12744, em12744, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12744, agent12744, tp12744, tm12744, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12744, agent12744, scalar12744, tp12744, tm12744, ep12744, em12744, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12744, agent12744, tp12744, tm12744, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12744, agent12744, scalar12744, tp12744, tm12744, ep12744, em12744, dsL]

theorem negative12744 :
    Eminus aL (agent12744.root+dsL) scalar12744.worldRadius world12744.frame
      agent12744.frame tm12744 ≤ -em12744 := by
  apply negative_check (lo := (34210221644711463253 / 50000000000000000000)) (hi := (68420443289422926507 / 100000000000000000000))
    (y := (-((35841415458234663877 / 50000000000000000000)))) (u := (48829853449174077801 / 100000000000000000000))
  · norm_num [world12744, agent12744, scalar12744, tp12744, tm12744, ep12744, em12744, dsL]
  · norm_num [world12744, agent12744, scalar12744, tp12744, tm12744, ep12744, em12744, dsL]
  · norm_num [world12744, agent12744, scalar12744, tp12744, tm12744, ep12744, em12744, dsL]
  · norm_num [world12744, agent12744, scalar12744, tp12744, tm12744, ep12744, em12744, dsL]
  · norm_num [world12744, agent12744, scalar12744, tp12744, tm12744, ep12744, em12744, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12744, agent12744, tp12744, tm12744, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12744, agent12744, tp12744, tm12744, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12744, agent12744, scalar12744, tp12744, tm12744, ep12744, em12744, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12744, agent12744, tp12744, tm12744, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12744, agent12744, scalar12744, tp12744, tm12744, ep12744, em12744, dsL]

theorem tails12744 :
    exp (-((12744:ℝ)*ep12744)) ≤ scalar12744.upperTail ∧
    exp (-((12744:ℝ)*em12744)) ≤ scalar12744.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12744:ℝ)) (by norm_num [ep12744]) ?_)
      (show bp12744^8 ≤ scalar12744.upperTail by norm_num [bp12744, scalar12744])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12744, bp12744, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12744:ℝ)) (by norm_num [em12744]) ?_)
      (show bm12744^8 ≤ scalar12744.lowerTail by norm_num [bm12744, scalar12744])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12744, bm12744, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12744 :
    agent12744.root+dsL+scalar12744.worldRadius < √(1/100/aL) ∧
    2*(agent12744.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12744, agent12744, scalar12744, tp12744, tm12744, ep12744, em12744, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12744, agent12744, scalar12744, tp12744, tm12744, ep12744, em12744, dsL]

noncomputable def master12744 : MasterCertificate 12744 world12744 agent12744 :=
  master scalar12744 dsL tp12744 tm12744 ep12744 em12744
    (by norm_num [dsL]) (by norm_num [tp12744]) (by norm_num [tm12744])
    (by norm_num [ep12744]) (by norm_num [em12744])
    positive12744 negative12744 tails12744.1 tails12744.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12744.1 tailGuards12744.2

theorem preserves12744 : master12744.toScalarCertificate = scalar12744 := rfl

noncomputable def tp12745 : ℝ := (1160296969 / 5000000000)
noncomputable def tm12745 : ℝ := (-((6071964267 / 10000000000)))
noncomputable def ep12745 : ℝ := (51547274565275459 / 100000000000000000000)
noncomputable def em12745 : ℝ := (12554020959663677 / 25000000000000000000)
noncomputable def bp12745 : ℝ := (43989794686366441563 / 100000000000000000000)
noncomputable def bm12745 : ℝ := (5616584049047545099 / 12500000000000000000)

theorem positive12745 :
    Eplus aL (agent12745.root+dsL) scalar12745.worldRadius world12745.frame
      agent12745.frame tp12745 ≤ -ep12745 := by
  apply positive_check (eT := (115608409446483599007 / 100000000000000000000)) (y := (37893815120993142337 / 100000000000000000000)) (u := (73036634420006627033 / 50000000000000000000))
  · norm_num [world12745, agent12745, scalar12745, tp12745, tm12745, ep12745, em12745, dsL]
  · norm_num [world12745, agent12745, scalar12745, tp12745, tm12745, ep12745, em12745, dsL]
  · norm_num [world12745, agent12745, scalar12745, tp12745, tm12745, ep12745, em12745, dsL]
  · norm_num [world12745, agent12745, scalar12745, tp12745, tm12745, ep12745, em12745, dsL]
  · norm_num [world12745, agent12745, scalar12745, tp12745, tm12745, ep12745, em12745, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12745, agent12745, tp12745, tm12745, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12745, agent12745, scalar12745, tp12745, tm12745, ep12745, em12745, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12745, agent12745, tp12745, tm12745, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12745, agent12745, scalar12745, tp12745, tm12745, ep12745, em12745, dsL]

theorem negative12745 :
    Eminus aL (agent12745.root+dsL) scalar12745.worldRadius world12745.frame
      agent12745.frame tm12745 ≤ -em12745 := by
  apply negative_check (lo := (2736809841686723707 / 4000000000000000000)) (hi := (17105061510542023169 / 25000000000000000000))
    (y := (-((71682884613267646177 / 100000000000000000000)))) (u := (48829827229113191683 / 100000000000000000000))
  · norm_num [world12745, agent12745, scalar12745, tp12745, tm12745, ep12745, em12745, dsL]
  · norm_num [world12745, agent12745, scalar12745, tp12745, tm12745, ep12745, em12745, dsL]
  · norm_num [world12745, agent12745, scalar12745, tp12745, tm12745, ep12745, em12745, dsL]
  · norm_num [world12745, agent12745, scalar12745, tp12745, tm12745, ep12745, em12745, dsL]
  · norm_num [world12745, agent12745, scalar12745, tp12745, tm12745, ep12745, em12745, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12745, agent12745, tp12745, tm12745, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12745, agent12745, tp12745, tm12745, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12745, agent12745, scalar12745, tp12745, tm12745, ep12745, em12745, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12745, agent12745, tp12745, tm12745, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12745, agent12745, scalar12745, tp12745, tm12745, ep12745, em12745, dsL]

theorem tails12745 :
    exp (-((12745:ℝ)*ep12745)) ≤ scalar12745.upperTail ∧
    exp (-((12745:ℝ)*em12745)) ≤ scalar12745.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12745:ℝ)) (by norm_num [ep12745]) ?_)
      (show bp12745^8 ≤ scalar12745.upperTail by norm_num [bp12745, scalar12745])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12745, bp12745, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12745:ℝ)) (by norm_num [em12745]) ?_)
      (show bm12745^8 ≤ scalar12745.lowerTail by norm_num [bm12745, scalar12745])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12745, bm12745, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12745 :
    agent12745.root+dsL+scalar12745.worldRadius < √(1/100/aL) ∧
    2*(agent12745.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12745, agent12745, scalar12745, tp12745, tm12745, ep12745, em12745, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12745, agent12745, scalar12745, tp12745, tm12745, ep12745, em12745, dsL]

noncomputable def master12745 : MasterCertificate 12745 world12745 agent12745 :=
  master scalar12745 dsL tp12745 tm12745 ep12745 em12745
    (by norm_num [dsL]) (by norm_num [tp12745]) (by norm_num [tm12745])
    (by norm_num [ep12745]) (by norm_num [em12745])
    positive12745 negative12745 tails12745.1 tails12745.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12745.1 tailGuards12745.2

theorem preserves12745 : master12745.toScalarCertificate = scalar12745 := rfl

noncomputable def tp12746 : ℝ := (464135537 / 2000000000)
noncomputable def tm12746 : ℝ := (-((3036071777 / 5000000000)))
noncomputable def ep12746 : ℝ := (51549842353157113 / 100000000000000000000)
noncomputable def em12746 : ℝ := (25109142001310103 / 50000000000000000000)
noncomputable def bp12746 : ℝ := (43985160809092305089 / 100000000000000000000)
noncomputable def bm12746 : ℝ := (22464138551932083639 / 50000000000000000000)

theorem positive12746 :
    Eplus aL (agent12746.root+dsL) scalar12746.worldRadius world12746.frame
      agent12746.frame tp12746 ≤ -ep12746 := by
  apply positive_check (eT := (7225540366437633371 / 6250000000000000000)) (y := (37894591428543642117 / 100000000000000000000)) (u := (73037201411115055011 / 50000000000000000000))
  · norm_num [world12746, agent12746, scalar12746, tp12746, tm12746, ep12746, em12746, dsL]
  · norm_num [world12746, agent12746, scalar12746, tp12746, tm12746, ep12746, em12746, dsL]
  · norm_num [world12746, agent12746, scalar12746, tp12746, tm12746, ep12746, em12746, dsL]
  · norm_num [world12746, agent12746, scalar12746, tp12746, tm12746, ep12746, em12746, dsL]
  · norm_num [world12746, agent12746, scalar12746, tp12746, tm12746, ep12746, em12746, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12746, agent12746, tp12746, tm12746, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12746, agent12746, scalar12746, tp12746, tm12746, ep12746, em12746, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12746, agent12746, tp12746, tm12746, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12746, agent12746, scalar12746, tp12746, tm12746, ep12746, em12746, dsL]

theorem negative12746 :
    Eminus aL (agent12746.root+dsL) scalar12746.worldRadius world12746.frame
      agent12746.frame tm12746 ≤ -em12746 := by
  apply negative_check (lo := (213812657224000163 / 312500000000000000)) (hi := (68420050311680052161 / 100000000000000000000))
    (y := (-((17920733790031691837 / 25000000000000000000)))) (u := (9765960509435090209 / 20000000000000000000))
  · norm_num [world12746, agent12746, scalar12746, tp12746, tm12746, ep12746, em12746, dsL]
  · norm_num [world12746, agent12746, scalar12746, tp12746, tm12746, ep12746, em12746, dsL]
  · norm_num [world12746, agent12746, scalar12746, tp12746, tm12746, ep12746, em12746, dsL]
  · norm_num [world12746, agent12746, scalar12746, tp12746, tm12746, ep12746, em12746, dsL]
  · norm_num [world12746, agent12746, scalar12746, tp12746, tm12746, ep12746, em12746, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12746, agent12746, tp12746, tm12746, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12746, agent12746, tp12746, tm12746, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12746, agent12746, scalar12746, tp12746, tm12746, ep12746, em12746, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12746, agent12746, tp12746, tm12746, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12746, agent12746, scalar12746, tp12746, tm12746, ep12746, em12746, dsL]

theorem tails12746 :
    exp (-((12746:ℝ)*ep12746)) ≤ scalar12746.upperTail ∧
    exp (-((12746:ℝ)*em12746)) ≤ scalar12746.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12746:ℝ)) (by norm_num [ep12746]) ?_)
      (show bp12746^8 ≤ scalar12746.upperTail by norm_num [bp12746, scalar12746])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12746, bp12746, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12746:ℝ)) (by norm_num [em12746]) ?_)
      (show bm12746^8 ≤ scalar12746.lowerTail by norm_num [bm12746, scalar12746])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12746, bm12746, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12746 :
    agent12746.root+dsL+scalar12746.worldRadius < √(1/100/aL) ∧
    2*(agent12746.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12746, agent12746, scalar12746, tp12746, tm12746, ep12746, em12746, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12746, agent12746, scalar12746, tp12746, tm12746, ep12746, em12746, dsL]

noncomputable def master12746 : MasterCertificate 12746 world12746 agent12746 :=
  master scalar12746 dsL tp12746 tm12746 ep12746 em12746
    (by norm_num [dsL]) (by norm_num [tp12746]) (by norm_num [tm12746])
    (by norm_num [ep12746]) (by norm_num [em12746])
    positive12746 negative12746 tails12746.1 tails12746.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12746.1 tailGuards12746.2

theorem preserves12746 : master12746.toScalarCertificate = scalar12746 := rfl

noncomputable def tp12747 : ℝ := (1160380727 / 5000000000)
noncomputable def tm12747 : ℝ := (-((3036161489 / 5000000000)))
noncomputable def ep12747 : ℝ := (1611012783619867 / 3125000000000000000)
noncomputable def em12747 : ℝ := (50220483211915871 / 100000000000000000000)
noncomputable def bp12747 : ℝ := (21990263942042844197 / 50000000000000000000)
noncomputable def bm12747 : ℝ := (4492388268155114449 / 10000000000000000000)

theorem positive12747 :
    Eplus aL (agent12747.root+dsL) scalar12747.worldRadius world12747.frame
      agent12747.frame tp12747 ≤ -ep12747 := by
  apply positive_check (eT := (57804441235634205831 / 50000000000000000000)) (y := (4736921047727780491 / 12500000000000000000)) (u := (912972110978131151 / 625000000000000000))
  · norm_num [world12747, agent12747, scalar12747, tp12747, tm12747, ep12747, em12747, dsL]
  · norm_num [world12747, agent12747, scalar12747, tp12747, tm12747, ep12747, em12747, dsL]
  · norm_num [world12747, agent12747, scalar12747, tp12747, tm12747, ep12747, em12747, dsL]
  · norm_num [world12747, agent12747, scalar12747, tp12747, tm12747, ep12747, em12747, dsL]
  · norm_num [world12747, agent12747, scalar12747, tp12747, tm12747, ep12747, em12747, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12747, agent12747, tp12747, tm12747, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12747, agent12747, scalar12747, tp12747, tm12747, ep12747, em12747, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12747, agent12747, tp12747, tm12747, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12747, agent12747, scalar12747, tp12747, tm12747, ep12747, em12747, dsL]

theorem negative12747 :
    Eminus aL (agent12747.root+dsL) scalar12747.worldRadius world12747.frame
      agent12747.frame tm12747 ≤ -em12747 := by
  apply negative_check (lo := (68419853938406455319 / 100000000000000000000)) (hi := (1710496348460161383 / 2500000000000000000))
    (y := (-((17920746927078777059 / 25000000000000000000)))) (u := (24414888444002791893 / 50000000000000000000))
  · norm_num [world12747, agent12747, scalar12747, tp12747, tm12747, ep12747, em12747, dsL]
  · norm_num [world12747, agent12747, scalar12747, tp12747, tm12747, ep12747, em12747, dsL]
  · norm_num [world12747, agent12747, scalar12747, tp12747, tm12747, ep12747, em12747, dsL]
  · norm_num [world12747, agent12747, scalar12747, tp12747, tm12747, ep12747, em12747, dsL]
  · norm_num [world12747, agent12747, scalar12747, tp12747, tm12747, ep12747, em12747, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12747, agent12747, tp12747, tm12747, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12747, agent12747, tp12747, tm12747, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12747, agent12747, scalar12747, tp12747, tm12747, ep12747, em12747, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12747, agent12747, tp12747, tm12747, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12747, agent12747, scalar12747, tp12747, tm12747, ep12747, em12747, dsL]

theorem tails12747 :
    exp (-((12747:ℝ)*ep12747)) ≤ scalar12747.upperTail ∧
    exp (-((12747:ℝ)*em12747)) ≤ scalar12747.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12747:ℝ)) (by norm_num [ep12747]) ?_)
      (show bp12747^8 ≤ scalar12747.upperTail by norm_num [bp12747, scalar12747])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12747, bp12747, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12747:ℝ)) (by norm_num [em12747]) ?_)
      (show bm12747^8 ≤ scalar12747.lowerTail by norm_num [bm12747, scalar12747])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12747, bm12747, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12747 :
    agent12747.root+dsL+scalar12747.worldRadius < √(1/100/aL) ∧
    2*(agent12747.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12747, agent12747, scalar12747, tp12747, tm12747, ep12747, em12747, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12747, agent12747, scalar12747, tp12747, tm12747, ep12747, em12747, dsL]

noncomputable def master12747 : MasterCertificate 12747 world12747 agent12747 :=
  master scalar12747 dsL tp12747 tm12747 ep12747 em12747
    (by norm_num [dsL]) (by norm_num [tp12747]) (by norm_num [tm12747])
    (by norm_num [ep12747]) (by norm_num [em12747])
    positive12747 negative12747 tails12747.1 tails12747.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12747.1 tailGuards12747.2

theorem preserves12747 : master12747.toScalarCertificate = scalar12747 := rfl

noncomputable def tp12748 : ℝ := (1160422541 / 5000000000)
noncomputable def tm12748 : ℝ := (-((607250233 / 1000000000)))
noncomputable def ep12748 : ℝ := (12888743455339643 / 25000000000000000000)
noncomputable def em12748 : ℝ := (1255567014135961 / 2500000000000000000)
noncomputable def bp12748 : ℝ := (43975896550380469723 / 100000000000000000000)
noncomputable def bm12748 : ℝ := (4491948977043460163 / 10000000000000000000)

theorem positive12748 :
    Eplus aL (agent12748.root+dsL) scalar12748.worldRadius world12748.frame
      agent12748.frame tp12748 ≤ -ep12748 := by
  apply positive_check (eT := (115609118093524315943 / 100000000000000000000)) (y := (37896143524001759341 / 100000000000000000000)) (u := (29215334010799308167 / 20000000000000000000))
  · norm_num [world12748, agent12748, scalar12748, tp12748, tm12748, ep12748, em12748, dsL]
  · norm_num [world12748, agent12748, scalar12748, tp12748, tm12748, ep12748, em12748, dsL]
  · norm_num [world12748, agent12748, scalar12748, tp12748, tm12748, ep12748, em12748, dsL]
  · norm_num [world12748, agent12748, scalar12748, tp12748, tm12748, ep12748, em12748, dsL]
  · norm_num [world12748, agent12748, scalar12748, tp12748, tm12748, ep12748, em12748, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12748, agent12748, tp12748, tm12748, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12748, agent12748, scalar12748, tp12748, tm12748, ep12748, em12748, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12748, agent12748, tp12748, tm12748, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12748, agent12748, scalar12748, tp12748, tm12748, ep12748, em12748, dsL]

theorem negative12748 :
    Eminus aL (agent12748.root+dsL) scalar12748.worldRadius world12748.frame
      agent12748.frame tm12748 ≤ -em12748 := by
  apply negative_check (lo := (34209828908073948421 / 50000000000000000000)) (hi := (68419657816147896843 / 100000000000000000000))
    (y := (-((7168304055022191131 / 10000000000000000000)))) (u := (9765950217085441153 / 20000000000000000000))
  · norm_num [world12748, agent12748, scalar12748, tp12748, tm12748, ep12748, em12748, dsL]
  · norm_num [world12748, agent12748, scalar12748, tp12748, tm12748, ep12748, em12748, dsL]
  · norm_num [world12748, agent12748, scalar12748, tp12748, tm12748, ep12748, em12748, dsL]
  · norm_num [world12748, agent12748, scalar12748, tp12748, tm12748, ep12748, em12748, dsL]
  · norm_num [world12748, agent12748, scalar12748, tp12748, tm12748, ep12748, em12748, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12748, agent12748, tp12748, tm12748, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12748, agent12748, tp12748, tm12748, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12748, agent12748, scalar12748, tp12748, tm12748, ep12748, em12748, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12748, agent12748, tp12748, tm12748, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12748, agent12748, scalar12748, tp12748, tm12748, ep12748, em12748, dsL]

theorem tails12748 :
    exp (-((12748:ℝ)*ep12748)) ≤ scalar12748.upperTail ∧
    exp (-((12748:ℝ)*em12748)) ≤ scalar12748.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12748:ℝ)) (by norm_num [ep12748]) ?_)
      (show bp12748^8 ≤ scalar12748.upperTail by norm_num [bp12748, scalar12748])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12748, bp12748, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12748:ℝ)) (by norm_num [em12748]) ?_)
      (show bm12748^8 ≤ scalar12748.lowerTail by norm_num [bm12748, scalar12748])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12748, bm12748, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12748 :
    agent12748.root+dsL+scalar12748.worldRadius < √(1/100/aL) ∧
    2*(agent12748.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12748, agent12748, scalar12748, tp12748, tm12748, ep12748, em12748, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12748, agent12748, scalar12748, tp12748, tm12748, ep12748, em12748, dsL]

noncomputable def master12748 : MasterCertificate 12748 world12748 agent12748 :=
  master scalar12748 dsL tp12748 tm12748 ep12748 em12748
    (by norm_num [dsL]) (by norm_num [tp12748]) (by norm_num [tm12748])
    (by norm_num [ep12748]) (by norm_num [em12748])
    positive12748 negative12748 tails12748.1 tails12748.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12748.1 tailGuards12748.2

theorem preserves12748 : master12748.toScalarCertificate = scalar12748 := rfl

noncomputable def tp12749 : ℝ := (2320928737 / 10000000000)
noncomputable def tm12749 : ℝ := (-((94885649 / 156250000)))
noncomputable def ep12749 : ℝ := (51557538132169931 / 100000000000000000000)
noncomputable def em12749 : ℝ := (50224877501862573 / 100000000000000000000)
noncomputable def bp12749 : ℝ := (4397126572705475837 / 10000000000000000000)
noncomputable def bm12749 : ℝ := (8983019468139168009 / 20000000000000000000)

theorem positive12749 :
    Eplus aL (agent12749.root+dsL) scalar12749.worldRadius world12749.frame
      agent12749.frame tp12749 ≤ -ep12749 := by
  apply positive_check (eT := (57804676971833659973 / 50000000000000000000)) (y := (3789691940119045069 / 10000000000000000000)) (u := (18259725429244287789 / 12500000000000000000))
  · norm_num [world12749, agent12749, scalar12749, tp12749, tm12749, ep12749, em12749, dsL]
  · norm_num [world12749, agent12749, scalar12749, tp12749, tm12749, ep12749, em12749, dsL]
  · norm_num [world12749, agent12749, scalar12749, tp12749, tm12749, ep12749, em12749, dsL]
  · norm_num [world12749, agent12749, scalar12749, tp12749, tm12749, ep12749, em12749, dsL]
  · norm_num [world12749, agent12749, scalar12749, tp12749, tm12749, ep12749, em12749, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12749, agent12749, tp12749, tm12749, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12749, agent12749, scalar12749, tp12749, tm12749, ep12749, em12749, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12749, agent12749, tp12749, tm12749, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12749, agent12749, scalar12749, tp12749, tm12749, ep12749, em12749, dsL]

theorem negative12749 :
    Eminus aL (agent12749.root+dsL) scalar12749.worldRadius world12749.frame
      agent12749.frame tm12749 ≤ -em12749 := by
  apply negative_check (lo := (34209731130623758539 / 50000000000000000000)) (hi := (68419462261247517079 / 100000000000000000000))
    (y := (-((71683092652325324063 / 100000000000000000000)))) (u := (24414862822053213389 / 50000000000000000000))
  · norm_num [world12749, agent12749, scalar12749, tp12749, tm12749, ep12749, em12749, dsL]
  · norm_num [world12749, agent12749, scalar12749, tp12749, tm12749, ep12749, em12749, dsL]
  · norm_num [world12749, agent12749, scalar12749, tp12749, tm12749, ep12749, em12749, dsL]
  · norm_num [world12749, agent12749, scalar12749, tp12749, tm12749, ep12749, em12749, dsL]
  · norm_num [world12749, agent12749, scalar12749, tp12749, tm12749, ep12749, em12749, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12749, agent12749, tp12749, tm12749, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12749, agent12749, tp12749, tm12749, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12749, agent12749, scalar12749, tp12749, tm12749, ep12749, em12749, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12749, agent12749, tp12749, tm12749, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12749, agent12749, scalar12749, tp12749, tm12749, ep12749, em12749, dsL]

theorem tails12749 :
    exp (-((12749:ℝ)*ep12749)) ≤ scalar12749.upperTail ∧
    exp (-((12749:ℝ)*em12749)) ≤ scalar12749.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12749:ℝ)) (by norm_num [ep12749]) ?_)
      (show bp12749^8 ≤ scalar12749.upperTail by norm_num [bp12749, scalar12749])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12749, bp12749, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12749:ℝ)) (by norm_num [em12749]) ?_)
      (show bm12749^8 ≤ scalar12749.lowerTail by norm_num [bm12749, scalar12749])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12749, bm12749, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12749 :
    agent12749.root+dsL+scalar12749.worldRadius < √(1/100/aL) ∧
    2*(agent12749.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12749, agent12749, scalar12749, tp12749, tm12749, ep12749, em12749, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12749, agent12749, scalar12749, tp12749, tm12749, ep12749, em12749, dsL]

noncomputable def master12749 : MasterCertificate 12749 world12749 agent12749 :=
  master scalar12749 dsL tp12749 tm12749 ep12749 em12749
    (by norm_num [dsL]) (by norm_num [tp12749]) (by norm_num [tm12749])
    (by norm_num [ep12749]) (by norm_num [em12749])
    positive12749 negative12749 tails12749.1 tails12749.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12749.1 tailGuards12749.2

theorem preserves12749 : master12749.toScalarCertificate = scalar12749 := rfl

end BstLean.Part268
