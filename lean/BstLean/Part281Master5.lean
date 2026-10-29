import BstLean.Part261Checker
import BstLean.Part281Scalar5
namespace BstLean.Part281
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp11984 : ℝ := (1211394641 / 5000000000)
noncomputable def tm11984 : ℝ := (-((250503097 / 400000000)))
noncomputable def ep11984 : ℝ := (28091491764429823 / 50000000000000000000)
noncomputable def em11984 : ℝ := (13523412506840769 / 25000000000000000000)
noncomputable def bp11984 : ℝ := (43101124735727965211 / 100000000000000000000)
noncomputable def bm11984 : ℝ := (2223572273942190359 / 5000000000000000000)

theorem positive11984 :
    Eplus aL (agent11984.root+dsL) scalar11984.worldRadius world11984.frame
      agent11984.frame tp11984 ≤ -ep11984 := by
  apply positive_check (eT := (58331807444142169313 / 50000000000000000000)) (y := (39780869028615713689 / 100000000000000000000)) (u := (74427961341281303003 / 50000000000000000000))
  · norm_num [world11984, agent11984, scalar11984, tp11984, tm11984, ep11984, em11984, dsL]
  · norm_num [world11984, agent11984, scalar11984, tp11984, tm11984, ep11984, em11984, dsL]
  · norm_num [world11984, agent11984, scalar11984, tp11984, tm11984, ep11984, em11984, dsL]
  · norm_num [world11984, agent11984, scalar11984, tp11984, tm11984, ep11984, em11984, dsL]
  · norm_num [world11984, agent11984, scalar11984, tp11984, tm11984, ep11984, em11984, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11984, agent11984, tp11984, tm11984, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11984, agent11984, scalar11984, tp11984, tm11984, ep11984, em11984, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11984, agent11984, tp11984, tm11984, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11984, agent11984, scalar11984, tp11984, tm11984, ep11984, em11984, dsL]

theorem negative11984 :
    Eminus aL (agent11984.root+dsL) scalar11984.worldRadius world11984.frame
      agent11984.frame tm11984 ≤ -em11984 := by
  apply negative_check (lo := (2685598608722071291 / 4000000000000000000)) (hi := (16784991304512945569 / 25000000000000000000))
    (y := (-((18213405064889812143 / 25000000000000000000)))) (u := (48261492376494699627 / 100000000000000000000))
  · norm_num [world11984, agent11984, scalar11984, tp11984, tm11984, ep11984, em11984, dsL]
  · norm_num [world11984, agent11984, scalar11984, tp11984, tm11984, ep11984, em11984, dsL]
  · norm_num [world11984, agent11984, scalar11984, tp11984, tm11984, ep11984, em11984, dsL]
  · norm_num [world11984, agent11984, scalar11984, tp11984, tm11984, ep11984, em11984, dsL]
  · norm_num [world11984, agent11984, scalar11984, tp11984, tm11984, ep11984, em11984, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11984, agent11984, tp11984, tm11984, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11984, agent11984, tp11984, tm11984, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11984, agent11984, scalar11984, tp11984, tm11984, ep11984, em11984, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11984, agent11984, tp11984, tm11984, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11984, agent11984, scalar11984, tp11984, tm11984, ep11984, em11984, dsL]

theorem tails11984 :
    exp (-((11984:ℝ)*ep11984)) ≤ scalar11984.upperTail ∧
    exp (-((11984:ℝ)*em11984)) ≤ scalar11984.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11984:ℝ)) (by norm_num [ep11984]) ?_)
      (show bp11984^8 ≤ scalar11984.upperTail by norm_num [bp11984, scalar11984])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11984, bp11984, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11984:ℝ)) (by norm_num [em11984]) ?_)
      (show bm11984^8 ≤ scalar11984.lowerTail by norm_num [bm11984, scalar11984])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11984, bm11984, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11984 :
    agent11984.root+dsL+scalar11984.worldRadius < √(1/100/aL) ∧
    2*(agent11984.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11984, agent11984, scalar11984, tp11984, tm11984, ep11984, em11984, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11984, agent11984, scalar11984, tp11984, tm11984, ep11984, em11984, dsL]

noncomputable def master11984 : MasterCertificate 11984 world11984 agent11984 :=
  master scalar11984 dsL tp11984 tm11984 ep11984 em11984
    (by norm_num [dsL]) (by norm_num [tp11984]) (by norm_num [tm11984])
    (by norm_num [ep11984]) (by norm_num [em11984])
    positive11984 negative11984 tails11984.1 tails11984.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11984.1 tailGuards11984.2

theorem preserves11984 : master11984.toScalarCertificate = scalar11984 := rfl

noncomputable def tp11985 : ℝ := (1211441903 / 5000000000)
noncomputable def tm11985 : ℝ := (-((3131393551 / 5000000000)))
noncomputable def ep11985 : ℝ := (56185755250259091 / 100000000000000000000)
noncomputable def em11985 : ℝ := (54096038493745521 / 100000000000000000000)
noncomputable def bp11985 : ℝ := (21548154171469008409 / 50000000000000000000)
noncomputable def bm11985 : ℝ := (44466847401367197227 / 100000000000000000000)

theorem positive11985 :
    Eplus aL (agent11985.root+dsL) scalar11985.worldRadius world11985.frame
      agent11985.frame tp11985 ≤ -ep11985 := by
  apply positive_check (eT := (116663875690801303201 / 100000000000000000000)) (y := (39781485838339566243 / 100000000000000000000)) (u := (148856840843199891627 / 100000000000000000000))
  · norm_num [world11985, agent11985, scalar11985, tp11985, tm11985, ep11985, em11985, dsL]
  · norm_num [world11985, agent11985, scalar11985, tp11985, tm11985, ep11985, em11985, dsL]
  · norm_num [world11985, agent11985, scalar11985, tp11985, tm11985, ep11985, em11985, dsL]
  · norm_num [world11985, agent11985, scalar11985, tp11985, tm11985, ep11985, em11985, dsL]
  · norm_num [world11985, agent11985, scalar11985, tp11985, tm11985, ep11985, em11985, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11985, agent11985, tp11985, tm11985, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11985, agent11985, scalar11985, tp11985, tm11985, ep11985, em11985, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11985, agent11985, tp11985, tm11985, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11985, agent11985, scalar11985, tp11985, tm11985, ep11985, em11985, dsL]

theorem negative11985 :
    Eminus aL (agent11985.root+dsL) scalar11985.worldRadius world11985.frame
      agent11985.frame tm11985 ≤ -em11985 := by
  apply negative_check (lo := (67139725260362497049 / 100000000000000000000)) (hi := (1342794505207249941 / 2000000000000000000))
    (y := (-((72853228417329911729 / 100000000000000000000)))) (u := (24130840742886421839 / 50000000000000000000))
  · norm_num [world11985, agent11985, scalar11985, tp11985, tm11985, ep11985, em11985, dsL]
  · norm_num [world11985, agent11985, scalar11985, tp11985, tm11985, ep11985, em11985, dsL]
  · norm_num [world11985, agent11985, scalar11985, tp11985, tm11985, ep11985, em11985, dsL]
  · norm_num [world11985, agent11985, scalar11985, tp11985, tm11985, ep11985, em11985, dsL]
  · norm_num [world11985, agent11985, scalar11985, tp11985, tm11985, ep11985, em11985, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11985, agent11985, tp11985, tm11985, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11985, agent11985, tp11985, tm11985, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11985, agent11985, scalar11985, tp11985, tm11985, ep11985, em11985, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11985, agent11985, tp11985, tm11985, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11985, agent11985, scalar11985, tp11985, tm11985, ep11985, em11985, dsL]

theorem tails11985 :
    exp (-((11985:ℝ)*ep11985)) ≤ scalar11985.upperTail ∧
    exp (-((11985:ℝ)*em11985)) ≤ scalar11985.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11985:ℝ)) (by norm_num [ep11985]) ?_)
      (show bp11985^8 ≤ scalar11985.upperTail by norm_num [bp11985, scalar11985])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11985, bp11985, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11985:ℝ)) (by norm_num [em11985]) ?_)
      (show bm11985^8 ≤ scalar11985.lowerTail by norm_num [bm11985, scalar11985])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11985, bm11985, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11985 :
    agent11985.root+dsL+scalar11985.worldRadius < √(1/100/aL) ∧
    2*(agent11985.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11985, agent11985, scalar11985, tp11985, tm11985, ep11985, em11985, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11985, agent11985, scalar11985, tp11985, tm11985, ep11985, em11985, dsL]

noncomputable def master11985 : MasterCertificate 11985 world11985 agent11985 :=
  master scalar11985 dsL tp11985 tm11985 ep11985 em11985
    (by norm_num [dsL]) (by norm_num [tp11985]) (by norm_num [tm11985])
    (by norm_num [ep11985]) (by norm_num [em11985])
    positive11985 negative11985 tails11985.1 tails11985.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11985.1 tailGuards11985.2

theorem preserves11985 : master11985.toScalarCertificate = scalar11985 := rfl

noncomputable def tp11986 : ℝ := (1211489093 / 5000000000)
noncomputable def tm11986 : ℝ := (-((6262996617 / 10000000000)))
noncomputable def ep11986 : ℝ := (56188524121993267 / 100000000000000000000)
noncomputable def em11986 : ℝ := (6762303047164783 / 12500000000000000000)
noncomputable def bp11986 : ℝ := (21545747014782161587 / 50000000000000000000)
noncomputable def bm11986 : ℝ := (22231125627182865233 / 50000000000000000000)

theorem positive11986 :
    Eplus aL (agent11986.root+dsL) scalar11986.worldRadius world11986.frame
      agent11986.frame tp11986 ≤ -ep11986 := by
  apply positive_check (eT := (116664135466736391601 / 100000000000000000000)) (y := (39782100597957129653 / 100000000000000000000)) (u := (74428877978879125377 / 50000000000000000000))
  · norm_num [world11986, agent11986, scalar11986, tp11986, tm11986, ep11986, em11986, dsL]
  · norm_num [world11986, agent11986, scalar11986, tp11986, tm11986, ep11986, em11986, dsL]
  · norm_num [world11986, agent11986, scalar11986, tp11986, tm11986, ep11986, em11986, dsL]
  · norm_num [world11986, agent11986, scalar11986, tp11986, tm11986, ep11986, em11986, dsL]
  · norm_num [world11986, agent11986, scalar11986, tp11986, tm11986, ep11986, em11986, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11986, agent11986, tp11986, tm11986, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11986, agent11986, scalar11986, tp11986, tm11986, ep11986, em11986, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11986, agent11986, tp11986, tm11986, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11986, agent11986, scalar11986, tp11986, tm11986, ep11986, em11986, dsL]

theorem negative11986 :
    Eminus aL (agent11986.root+dsL) scalar11986.worldRadius world11986.frame
      agent11986.frame tm11986 ≤ -em11986 := by
  apply negative_check (lo := (537115887411544573 / 800000000000000000)) (hi := (33569742963221535813 / 50000000000000000000))
    (y := (-((4553302217118778963 / 6250000000000000000)))) (u := (48261871127251774921 / 100000000000000000000))
  · norm_num [world11986, agent11986, scalar11986, tp11986, tm11986, ep11986, em11986, dsL]
  · norm_num [world11986, agent11986, scalar11986, tp11986, tm11986, ep11986, em11986, dsL]
  · norm_num [world11986, agent11986, scalar11986, tp11986, tm11986, ep11986, em11986, dsL]
  · norm_num [world11986, agent11986, scalar11986, tp11986, tm11986, ep11986, em11986, dsL]
  · norm_num [world11986, agent11986, scalar11986, tp11986, tm11986, ep11986, em11986, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11986, agent11986, tp11986, tm11986, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11986, agent11986, tp11986, tm11986, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11986, agent11986, scalar11986, tp11986, tm11986, ep11986, em11986, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11986, agent11986, tp11986, tm11986, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11986, agent11986, scalar11986, tp11986, tm11986, ep11986, em11986, dsL]

theorem tails11986 :
    exp (-((11986:ℝ)*ep11986)) ≤ scalar11986.upperTail ∧
    exp (-((11986:ℝ)*em11986)) ≤ scalar11986.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11986:ℝ)) (by norm_num [ep11986]) ?_)
      (show bp11986^8 ≤ scalar11986.upperTail by norm_num [bp11986, scalar11986])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11986, bp11986, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11986:ℝ)) (by norm_num [em11986]) ?_)
      (show bm11986^8 ≤ scalar11986.lowerTail by norm_num [bm11986, scalar11986])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11986, bm11986, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11986 :
    agent11986.root+dsL+scalar11986.worldRadius < √(1/100/aL) ∧
    2*(agent11986.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11986, agent11986, scalar11986, tp11986, tm11986, ep11986, em11986, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11986, agent11986, scalar11986, tp11986, tm11986, ep11986, em11986, dsL]

noncomputable def master11986 : MasterCertificate 11986 world11986 agent11986 :=
  master scalar11986 dsL tp11986 tm11986 ep11986 em11986
    (by norm_num [dsL]) (by norm_num [tp11986]) (by norm_num [tm11986])
    (by norm_num [ep11986]) (by norm_num [em11986])
    positive11986 negative11986 tails11986.1 tails11986.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11986.1 tailGuards11986.2

theorem preserves11986 : master11986.toScalarCertificate = scalar11986 := rfl

noncomputable def tp11987 : ℝ := (1211536331 / 5000000000)
noncomputable def tm11987 : ℝ := (-((6263206143 / 10000000000)))
noncomputable def ep11987 : ℝ := (28095645848081353 / 50000000000000000000)
noncomputable def em11987 : ℝ := (27050404521107451 / 50000000000000000000)
noncomputable def bp11987 : ℝ := (861733615869089441 / 2000000000000000000)
noncomputable def bm11987 : ℝ := (44457656129062413091 / 100000000000000000000)

theorem positive11987 :
    Eplus aL (agent11987.root+dsL) scalar11987.worldRadius world11987.frame
      agent11987.frame tp11987 ≤ -ep11987 := by
  apply positive_check (eT := (93331516797768373 / 80000000000000000)) (y := (39782717725896148019 / 100000000000000000000)) (u := (148858674603394268381 / 100000000000000000000))
  · norm_num [world11987, agent11987, scalar11987, tp11987, tm11987, ep11987, em11987, dsL]
  · norm_num [world11987, agent11987, scalar11987, tp11987, tm11987, ep11987, em11987, dsL]
  · norm_num [world11987, agent11987, scalar11987, tp11987, tm11987, ep11987, em11987, dsL]
  · norm_num [world11987, agent11987, scalar11987, tp11987, tm11987, ep11987, em11987, dsL]
  · norm_num [world11987, agent11987, scalar11987, tp11987, tm11987, ep11987, em11987, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11987, agent11987, tp11987, tm11987, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11987, agent11987, scalar11987, tp11987, tm11987, ep11987, em11987, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11987, agent11987, tp11987, tm11987, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11987, agent11987, scalar11987, tp11987, tm11987, ep11987, em11987, dsL]

theorem negative11987 :
    Eminus aL (agent11987.root+dsL) scalar11987.worldRadius world11987.frame
      agent11987.frame tm11987 ≤ -em11987 := by
  apply negative_check (lo := (67139246477390880189 / 100000000000000000000)) (hi := (6713924647739088019 / 10000000000000000000))
    (y := (-((72852444043834968309 / 100000000000000000000)))) (u := (24131030019547633059 / 50000000000000000000))
  · norm_num [world11987, agent11987, scalar11987, tp11987, tm11987, ep11987, em11987, dsL]
  · norm_num [world11987, agent11987, scalar11987, tp11987, tm11987, ep11987, em11987, dsL]
  · norm_num [world11987, agent11987, scalar11987, tp11987, tm11987, ep11987, em11987, dsL]
  · norm_num [world11987, agent11987, scalar11987, tp11987, tm11987, ep11987, em11987, dsL]
  · norm_num [world11987, agent11987, scalar11987, tp11987, tm11987, ep11987, em11987, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11987, agent11987, tp11987, tm11987, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11987, agent11987, tp11987, tm11987, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11987, agent11987, scalar11987, tp11987, tm11987, ep11987, em11987, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11987, agent11987, tp11987, tm11987, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11987, agent11987, scalar11987, tp11987, tm11987, ep11987, em11987, dsL]

theorem tails11987 :
    exp (-((11987:ℝ)*ep11987)) ≤ scalar11987.upperTail ∧
    exp (-((11987:ℝ)*em11987)) ≤ scalar11987.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11987:ℝ)) (by norm_num [ep11987]) ?_)
      (show bp11987^8 ≤ scalar11987.upperTail by norm_num [bp11987, scalar11987])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11987, bp11987, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11987:ℝ)) (by norm_num [em11987]) ?_)
      (show bm11987^8 ≤ scalar11987.lowerTail by norm_num [bm11987, scalar11987])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11987, bm11987, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11987 :
    agent11987.root+dsL+scalar11987.worldRadius < √(1/100/aL) ∧
    2*(agent11987.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11987, agent11987, scalar11987, tp11987, tm11987, ep11987, em11987, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11987, agent11987, scalar11987, tp11987, tm11987, ep11987, em11987, dsL]

noncomputable def master11987 : MasterCertificate 11987 world11987 agent11987 :=
  master scalar11987 dsL tp11987 tm11987 ep11987 em11987
    (by norm_num [dsL]) (by norm_num [tp11987]) (by norm_num [tm11987])
    (by norm_num [ep11987]) (by norm_num [em11987])
    positive11987 negative11987 tails11987.1 tails11987.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11987.1 tailGuards11987.2

theorem preserves11987 : master11987.toScalarCertificate = scalar11987 := rfl

noncomputable def tp11988 : ℝ := (605791749 / 2500000000)
noncomputable def tm11988 : ℝ := (-((12526831 / 20000000)))
noncomputable def ep11988 : ℝ := (1123881155792327 / 2000000000000000000)
noncomputable def em11988 : ℝ := (27051596177729999 / 50000000000000000000)
noncomputable def bp11988 : ℝ := (4308186875281623729 / 10000000000000000000)
noncomputable def bm11988 : ℝ := (44453062114020624543 / 100000000000000000000)

theorem positive11988 :
    Eplus aL (agent11988.root+dsL) scalar11988.worldRadius world11988.frame
      agent11988.frame tp11988 ≤ -ep11988 := by
  apply positive_check (eT := (58332327757998920299 / 50000000000000000000)) (y := (1989166636789796747 / 5000000000000000000)) (u := (148859590101794970867 / 100000000000000000000))
  · norm_num [world11988, agent11988, scalar11988, tp11988, tm11988, ep11988, em11988, dsL]
  · norm_num [world11988, agent11988, scalar11988, tp11988, tm11988, ep11988, em11988, dsL]
  · norm_num [world11988, agent11988, scalar11988, tp11988, tm11988, ep11988, em11988, dsL]
  · norm_num [world11988, agent11988, scalar11988, tp11988, tm11988, ep11988, em11988, dsL]
  · norm_num [world11988, agent11988, scalar11988, tp11988, tm11988, ep11988, em11988, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11988, agent11988, tp11988, tm11988, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11988, agent11988, scalar11988, tp11988, tm11988, ep11988, em11988, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11988, agent11988, tp11988, tm11988, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11988, agent11988, scalar11988, tp11988, tm11988, ep11988, em11988, dsL]

theorem negative11988 :
    Eminus aL (agent11988.root+dsL) scalar11988.worldRadius world11988.frame
      agent11988.frame tm11988 ≤ -em11988 := by
  apply negative_check (lo := (67139007681948541229 / 100000000000000000000)) (hi := (6713900768194854123 / 10000000000000000000))
    (y := (-((9106506463151551863 / 12500000000000000000)))) (u := (24131124695084143927 / 50000000000000000000))
  · norm_num [world11988, agent11988, scalar11988, tp11988, tm11988, ep11988, em11988, dsL]
  · norm_num [world11988, agent11988, scalar11988, tp11988, tm11988, ep11988, em11988, dsL]
  · norm_num [world11988, agent11988, scalar11988, tp11988, tm11988, ep11988, em11988, dsL]
  · norm_num [world11988, agent11988, scalar11988, tp11988, tm11988, ep11988, em11988, dsL]
  · norm_num [world11988, agent11988, scalar11988, tp11988, tm11988, ep11988, em11988, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11988, agent11988, tp11988, tm11988, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11988, agent11988, tp11988, tm11988, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11988, agent11988, scalar11988, tp11988, tm11988, ep11988, em11988, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11988, agent11988, tp11988, tm11988, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11988, agent11988, scalar11988, tp11988, tm11988, ep11988, em11988, dsL]

theorem tails11988 :
    exp (-((11988:ℝ)*ep11988)) ≤ scalar11988.upperTail ∧
    exp (-((11988:ℝ)*em11988)) ≤ scalar11988.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11988:ℝ)) (by norm_num [ep11988]) ?_)
      (show bp11988^8 ≤ scalar11988.upperTail by norm_num [bp11988, scalar11988])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11988, bp11988, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11988:ℝ)) (by norm_num [em11988]) ?_)
      (show bm11988^8 ≤ scalar11988.lowerTail by norm_num [bm11988, scalar11988])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11988, bm11988, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11988 :
    agent11988.root+dsL+scalar11988.worldRadius < √(1/100/aL) ∧
    2*(agent11988.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11988, agent11988, scalar11988, tp11988, tm11988, ep11988, em11988, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11988, agent11988, scalar11988, tp11988, tm11988, ep11988, em11988, dsL]

noncomputable def master11988 : MasterCertificate 11988 world11988 agent11988 :=
  master scalar11988 dsL tp11988 tm11988 ep11988 em11988
    (by norm_num [dsL]) (by norm_num [tp11988]) (by norm_num [tm11988])
    (by norm_num [ep11988]) (by norm_num [em11988])
    positive11988 negative11988 tails11988.1 tails11988.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11988.1 tailGuards11988.2

theorem preserves11988 : master11988.toScalarCertificate = scalar11988 := rfl

noncomputable def tp11989 : ℝ := (2423261293 / 10000000000)
noncomputable def tm11989 : ℝ := (-((3131812381 / 5000000000)))
noncomputable def ep11989 : ℝ := (878075353706381 / 1562500000000000000)
noncomputable def em11989 : ℝ := (10821114897111183 / 20000000000000000000)
noncomputable def bp11989 : ℝ := (10769264438998761937 / 25000000000000000000)
noncomputable def bm11989 : ℝ := (11112117274244379383 / 25000000000000000000)

theorem positive11989 :
    Eplus aL (agent11989.root+dsL) scalar11989.worldRadius world11989.frame
      agent11989.frame tp11989 ≤ -ep11989 := by
  apply positive_check (eT := (116664914802320216519 / 100000000000000000000)) (y := (4972993456242120693 / 12500000000000000000)) (u := (74430252731639563859 / 50000000000000000000))
  · norm_num [world11989, agent11989, scalar11989, tp11989, tm11989, ep11989, em11989, dsL]
  · norm_num [world11989, agent11989, scalar11989, tp11989, tm11989, ep11989, em11989, dsL]
  · norm_num [world11989, agent11989, scalar11989, tp11989, tm11989, ep11989, em11989, dsL]
  · norm_num [world11989, agent11989, scalar11989, tp11989, tm11989, ep11989, em11989, dsL]
  · norm_num [world11989, agent11989, scalar11989, tp11989, tm11989, ep11989, em11989, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11989, agent11989, tp11989, tm11989, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11989, agent11989, scalar11989, tp11989, tm11989, ep11989, em11989, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11989, agent11989, tp11989, tm11989, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11989, agent11989, scalar11989, tp11989, tm11989, ep11989, em11989, dsL]

theorem negative11989 :
    Eminus aL (agent11989.root+dsL) scalar11989.worldRadius world11989.frame
      agent11989.frame tm11989 ≤ -em11989 := by
  apply negative_check (lo := (67138769224071570467 / 100000000000000000000)) (hi := (16784692306017892617 / 25000000000000000000))
    (y := (-((72851659457123061463 / 100000000000000000000)))) (u := (24131219349145339143 / 50000000000000000000))
  · norm_num [world11989, agent11989, scalar11989, tp11989, tm11989, ep11989, em11989, dsL]
  · norm_num [world11989, agent11989, scalar11989, tp11989, tm11989, ep11989, em11989, dsL]
  · norm_num [world11989, agent11989, scalar11989, tp11989, tm11989, ep11989, em11989, dsL]
  · norm_num [world11989, agent11989, scalar11989, tp11989, tm11989, ep11989, em11989, dsL]
  · norm_num [world11989, agent11989, scalar11989, tp11989, tm11989, ep11989, em11989, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11989, agent11989, tp11989, tm11989, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11989, agent11989, tp11989, tm11989, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11989, agent11989, scalar11989, tp11989, tm11989, ep11989, em11989, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11989, agent11989, tp11989, tm11989, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11989, agent11989, scalar11989, tp11989, tm11989, ep11989, em11989, dsL]

theorem tails11989 :
    exp (-((11989:ℝ)*ep11989)) ≤ scalar11989.upperTail ∧
    exp (-((11989:ℝ)*em11989)) ≤ scalar11989.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11989:ℝ)) (by norm_num [ep11989]) ?_)
      (show bp11989^8 ≤ scalar11989.upperTail by norm_num [bp11989, scalar11989])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11989, bp11989, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11989:ℝ)) (by norm_num [em11989]) ?_)
      (show bm11989^8 ≤ scalar11989.lowerTail by norm_num [bm11989, scalar11989])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11989, bm11989, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11989 :
    agent11989.root+dsL+scalar11989.worldRadius < √(1/100/aL) ∧
    2*(agent11989.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11989, agent11989, scalar11989, tp11989, tm11989, ep11989, em11989, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11989, agent11989, scalar11989, tp11989, tm11989, ep11989, em11989, dsL]

noncomputable def master11989 : MasterCertificate 11989 world11989 agent11989 :=
  master scalar11989 dsL tp11989 tm11989 ep11989 em11989
    (by norm_num [dsL]) (by norm_num [tp11989]) (by norm_num [tm11989])
    (by norm_num [ep11989]) (by norm_num [em11989])
    positive11989 negative11989 tails11989.1 tails11989.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11989.1 tailGuards11989.2

theorem preserves11989 : master11989.toScalarCertificate = scalar11989 := rfl

noncomputable def tp11990 : ℝ := (2423355539 / 10000000000)
noncomputable def tm11990 : ℝ := (-((6263833623 / 10000000000)))
noncomputable def ep11990 : ℝ := (56199585468343549 / 100000000000000000000)
noncomputable def em11990 : ℝ := (54107954782312777 / 100000000000000000000)
noncomputable def bp11990 : ℝ := (10768062075104156921 / 25000000000000000000)
noncomputable def bm11990 : ℝ := (44443877511012200309 / 100000000000000000000)

theorem positive11990 :
    Eplus aL (agent11990.root+dsL) scalar11990.worldRadius world11990.frame
      agent11990.frame tp11990 ≤ -ep11990 := by
  apply positive_check (eT := (23333034750463598703 / 20000000000000000000)) (y := (19892281108663901603 / 50000000000000000000)) (u := (14886142031421472603 / 10000000000000000000))
  · norm_num [world11990, agent11990, scalar11990, tp11990, tm11990, ep11990, em11990, dsL]
  · norm_num [world11990, agent11990, scalar11990, tp11990, tm11990, ep11990, em11990, dsL]
  · norm_num [world11990, agent11990, scalar11990, tp11990, tm11990, ep11990, em11990, dsL]
  · norm_num [world11990, agent11990, scalar11990, tp11990, tm11990, ep11990, em11990, dsL]
  · norm_num [world11990, agent11990, scalar11990, tp11990, tm11990, ep11990, em11990, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11990, agent11990, tp11990, tm11990, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11990, agent11990, scalar11990, tp11990, tm11990, ep11990, em11990, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11990, agent11990, tp11990, tm11990, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11990, agent11990, scalar11990, tp11990, tm11990, ep11990, em11990, dsL]

theorem negative11990 :
    Eminus aL (agent11990.root+dsL) scalar11990.worldRadius world11990.frame
      agent11990.frame tm11990 ≤ -em11990 := by
  apply negative_check (lo := (1678463310261105883 / 2500000000000000000)) (hi := (67138532410444235321 / 100000000000000000000))
    (y := (-((14570252878769819977 / 20000000000000000000)))) (u := (48262629365837721931 / 100000000000000000000))
  · norm_num [world11990, agent11990, scalar11990, tp11990, tm11990, ep11990, em11990, dsL]
  · norm_num [world11990, agent11990, scalar11990, tp11990, tm11990, ep11990, em11990, dsL]
  · norm_num [world11990, agent11990, scalar11990, tp11990, tm11990, ep11990, em11990, dsL]
  · norm_num [world11990, agent11990, scalar11990, tp11990, tm11990, ep11990, em11990, dsL]
  · norm_num [world11990, agent11990, scalar11990, tp11990, tm11990, ep11990, em11990, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11990, agent11990, tp11990, tm11990, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11990, agent11990, tp11990, tm11990, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11990, agent11990, scalar11990, tp11990, tm11990, ep11990, em11990, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11990, agent11990, tp11990, tm11990, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11990, agent11990, scalar11990, tp11990, tm11990, ep11990, em11990, dsL]

theorem tails11990 :
    exp (-((11990:ℝ)*ep11990)) ≤ scalar11990.upperTail ∧
    exp (-((11990:ℝ)*em11990)) ≤ scalar11990.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11990:ℝ)) (by norm_num [ep11990]) ?_)
      (show bp11990^8 ≤ scalar11990.upperTail by norm_num [bp11990, scalar11990])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11990, bp11990, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11990:ℝ)) (by norm_num [em11990]) ?_)
      (show bm11990^8 ≤ scalar11990.lowerTail by norm_num [bm11990, scalar11990])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11990, bm11990, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11990 :
    agent11990.root+dsL+scalar11990.worldRadius < √(1/100/aL) ∧
    2*(agent11990.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11990, agent11990, scalar11990, tp11990, tm11990, ep11990, em11990, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11990, agent11990, scalar11990, tp11990, tm11990, ep11990, em11990, dsL]

noncomputable def master11990 : MasterCertificate 11990 world11990 agent11990 :=
  master scalar11990 dsL tp11990 tm11990 ep11990 em11990
    (by norm_num [dsL]) (by norm_num [tp11990]) (by norm_num [tm11990])
    (by norm_num [ep11990]) (by norm_num [em11990])
    positive11990 negative11990 tails11990.1 tails11990.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11990.1 tailGuards11990.2

theorem preserves11990 : master11990.toScalarCertificate = scalar11990 := rfl

noncomputable def tp11991 : ℝ := (1211724851 / 5000000000)
noncomputable def tm11991 : ℝ := (-((1566010683 / 2500000000)))
noncomputable def ep11991 : ℝ := (56202346329570077 / 100000000000000000000)
noncomputable def em11991 : ℝ := (13527583319204923 / 25000000000000000000)
noncomputable def bp11991 : ℝ := (8613488071192443929 / 20000000000000000000)
noncomputable def bm11991 : ℝ := (11109821833844152199 / 25000000000000000000)

theorem positive11991 :
    Eplus aL (agent11991.root+dsL) scalar11991.worldRadius world11991.frame
      agent11991.frame tp11991 ≤ -ep11991 := by
  apply positive_check (eT := (7291589508034151497 / 6250000000000000000)) (y := (39785175763594598179 / 100000000000000000000)) (u := (148862333650703629969 / 100000000000000000000))
  · norm_num [world11991, agent11991, scalar11991, tp11991, tm11991, ep11991, em11991, dsL]
  · norm_num [world11991, agent11991, scalar11991, tp11991, tm11991, ep11991, em11991, dsL]
  · norm_num [world11991, agent11991, scalar11991, tp11991, tm11991, ep11991, em11991, dsL]
  · norm_num [world11991, agent11991, scalar11991, tp11991, tm11991, ep11991, em11991, dsL]
  · norm_num [world11991, agent11991, scalar11991, tp11991, tm11991, ep11991, em11991, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11991, agent11991, tp11991, tm11991, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11991, agent11991, scalar11991, tp11991, tm11991, ep11991, em11991, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11991, agent11991, tp11991, tm11991, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11991, agent11991, scalar11991, tp11991, tm11991, ep11991, em11991, dsL]

theorem negative11991 :
    Eminus aL (agent11991.root+dsL) scalar11991.worldRadius world11991.frame
      agent11991.frame tm11991 ≤ -em11991 := by
  apply negative_check (lo := (67138294469570574087 / 100000000000000000000)) (hi := (8392286808696321761 / 12500000000000000000))
    (y := (-((14570174448196256069 / 20000000000000000000)))) (u := (9652563725898793273 / 20000000000000000000))
  · norm_num [world11991, agent11991, scalar11991, tp11991, tm11991, ep11991, em11991, dsL]
  · norm_num [world11991, agent11991, scalar11991, tp11991, tm11991, ep11991, em11991, dsL]
  · norm_num [world11991, agent11991, scalar11991, tp11991, tm11991, ep11991, em11991, dsL]
  · norm_num [world11991, agent11991, scalar11991, tp11991, tm11991, ep11991, em11991, dsL]
  · norm_num [world11991, agent11991, scalar11991, tp11991, tm11991, ep11991, em11991, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11991, agent11991, tp11991, tm11991, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11991, agent11991, tp11991, tm11991, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11991, agent11991, scalar11991, tp11991, tm11991, ep11991, em11991, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11991, agent11991, tp11991, tm11991, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11991, agent11991, scalar11991, tp11991, tm11991, ep11991, em11991, dsL]

theorem tails11991 :
    exp (-((11991:ℝ)*ep11991)) ≤ scalar11991.upperTail ∧
    exp (-((11991:ℝ)*em11991)) ≤ scalar11991.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11991:ℝ)) (by norm_num [ep11991]) ?_)
      (show bp11991^8 ≤ scalar11991.upperTail by norm_num [bp11991, scalar11991])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11991, bp11991, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11991:ℝ)) (by norm_num [em11991]) ?_)
      (show bm11991^8 ≤ scalar11991.lowerTail by norm_num [bm11991, scalar11991])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11991, bm11991, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11991 :
    agent11991.root+dsL+scalar11991.worldRadius < √(1/100/aL) ∧
    2*(agent11991.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11991, agent11991, scalar11991, tp11991, tm11991, ep11991, em11991, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11991, agent11991, scalar11991, tp11991, tm11991, ep11991, em11991, dsL]

noncomputable def master11991 : MasterCertificate 11991 world11991 agent11991 :=
  master scalar11991 dsL tp11991 tm11991 ep11991 em11991
    (by norm_num [dsL]) (by norm_num [tp11991]) (by norm_num [tm11991])
    (by norm_num [ep11991]) (by norm_num [em11991])
    positive11991 negative11991 tails11991.1 tails11991.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11991.1 tailGuards11991.2

theorem preserves11991 : master11991.toScalarCertificate = scalar11991 := rfl

noncomputable def tp11992 : ℝ := (605885963 / 2500000000)
noncomputable def tm11992 : ℝ := (-((6264251617 / 10000000000)))
noncomputable def ep11992 : ℝ := (28102553194070369 / 50000000000000000000)
noncomputable def em11992 : ℝ := (54112711008539273 / 100000000000000000000)
noncomputable def bp11992 : ℝ := (43062633169091736729 / 100000000000000000000)
noncomputable def bm11992 : ℝ := (11108674469417702203 / 25000000000000000000)

theorem positive11992 :
    Eplus aL (agent11992.root+dsL) scalar11992.worldRadius world11992.frame
      agent11992.frame tp11992 ≤ -ep11992 := by
  apply positive_check (eT := (58332845225219871261 / 50000000000000000000)) (y := (39785789693730720037 / 100000000000000000000)) (u := (1162994121595598737 / 781250000000000000))
  · norm_num [world11992, agent11992, scalar11992, tp11992, tm11992, ep11992, em11992, dsL]
  · norm_num [world11992, agent11992, scalar11992, tp11992, tm11992, ep11992, em11992, dsL]
  · norm_num [world11992, agent11992, scalar11992, tp11992, tm11992, ep11992, em11992, dsL]
  · norm_num [world11992, agent11992, scalar11992, tp11992, tm11992, ep11992, em11992, dsL]
  · norm_num [world11992, agent11992, scalar11992, tp11992, tm11992, ep11992, em11992, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11992, agent11992, tp11992, tm11992, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11992, agent11992, scalar11992, tp11992, tm11992, ep11992, em11992, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11992, agent11992, tp11992, tm11992, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11992, agent11992, scalar11992, tp11992, tm11992, ep11992, em11992, dsL]

theorem negative11992 :
    Eminus aL (agent11992.root+dsL) scalar11992.worldRadius world11992.frame
      agent11992.frame tm11992 ≤ -em11992 := by
  apply negative_check (lo := (67138057417066259183 / 100000000000000000000)) (hi := (4196128588566641199 / 6250000000000000000))
    (y := (-((14570095900426924163 / 20000000000000000000)))) (u := (48263008176703429739 / 100000000000000000000))
  · norm_num [world11992, agent11992, scalar11992, tp11992, tm11992, ep11992, em11992, dsL]
  · norm_num [world11992, agent11992, scalar11992, tp11992, tm11992, ep11992, em11992, dsL]
  · norm_num [world11992, agent11992, scalar11992, tp11992, tm11992, ep11992, em11992, dsL]
  · norm_num [world11992, agent11992, scalar11992, tp11992, tm11992, ep11992, em11992, dsL]
  · norm_num [world11992, agent11992, scalar11992, tp11992, tm11992, ep11992, em11992, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11992, agent11992, tp11992, tm11992, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11992, agent11992, tp11992, tm11992, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11992, agent11992, scalar11992, tp11992, tm11992, ep11992, em11992, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11992, agent11992, tp11992, tm11992, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11992, agent11992, scalar11992, tp11992, tm11992, ep11992, em11992, dsL]

theorem tails11992 :
    exp (-((11992:ℝ)*ep11992)) ≤ scalar11992.upperTail ∧
    exp (-((11992:ℝ)*em11992)) ≤ scalar11992.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11992:ℝ)) (by norm_num [ep11992]) ?_)
      (show bp11992^8 ≤ scalar11992.upperTail by norm_num [bp11992, scalar11992])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11992, bp11992, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11992:ℝ)) (by norm_num [em11992]) ?_)
      (show bm11992^8 ≤ scalar11992.lowerTail by norm_num [bm11992, scalar11992])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11992, bm11992, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11992 :
    agent11992.root+dsL+scalar11992.worldRadius < √(1/100/aL) ∧
    2*(agent11992.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11992, agent11992, scalar11992, tp11992, tm11992, ep11992, em11992, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11992, agent11992, scalar11992, tp11992, tm11992, ep11992, em11992, dsL]

noncomputable def master11992 : MasterCertificate 11992 world11992 agent11992 :=
  master scalar11992 dsL tp11992 tm11992 ep11992 em11992
    (by norm_num [dsL]) (by norm_num [tp11992]) (by norm_num [tm11992])
    (by norm_num [ep11992]) (by norm_num [em11992])
    positive11992 negative11992 tails11992.1 tails11992.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11992.1 tailGuards11992.2

theorem preserves11992 : master11992.toScalarCertificate = scalar11992 := rfl

noncomputable def tp11993 : ℝ := (2423637987 / 10000000000)
noncomputable def tm11993 : ℝ := (-((3132230169 / 5000000000)))
noncomputable def ep11993 : ℝ := (28103932184034097 / 50000000000000000000)
noncomputable def em11993 : ℝ := (54115086808397147 / 100000000000000000000)
noncomputable def bp11993 : ℝ := (43057827563438801887 / 100000000000000000000)
noncomputable def bm11993 : ℝ := (4443010991657441891 / 10000000000000000000)

theorem positive11993 :
    Eplus aL (agent11993.root+dsL) scalar11993.worldRadius world11993.frame
      agent11993.frame tp11993 ≤ -ep11993 := by
  apply positive_check (eT := (23333189740634696611 / 20000000000000000000)) (y := (19893201930187983033 / 50000000000000000000)) (u := (148864161835457779469 / 100000000000000000000))
  · norm_num [world11993, agent11993, scalar11993, tp11993, tm11993, ep11993, em11993, dsL]
  · norm_num [world11993, agent11993, scalar11993, tp11993, tm11993, ep11993, em11993, dsL]
  · norm_num [world11993, agent11993, scalar11993, tp11993, tm11993, ep11993, em11993, dsL]
  · norm_num [world11993, agent11993, scalar11993, tp11993, tm11993, ep11993, em11993, dsL]
  · norm_num [world11993, agent11993, scalar11993, tp11993, tm11993, ep11993, em11993, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11993, agent11993, tp11993, tm11993, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11993, agent11993, scalar11993, tp11993, tm11993, ep11993, em11993, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11993, agent11993, tp11993, tm11993, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11993, agent11993, scalar11993, tp11993, tm11993, ep11993, em11993, dsL]

theorem negative11993 :
    Eminus aL (agent11993.root+dsL) scalar11993.worldRadius world11993.frame
      agent11993.frame tm11993 ≤ -em11993 := by
  apply negative_check (lo := (2685512839865620667 / 4000000000000000000)) (hi := (16784455249160129169 / 25000000000000000000))
    (y := (-((36425042824346660561 / 50000000000000000000)))) (u := (48263198262596338107 / 100000000000000000000))
  · norm_num [world11993, agent11993, scalar11993, tp11993, tm11993, ep11993, em11993, dsL]
  · norm_num [world11993, agent11993, scalar11993, tp11993, tm11993, ep11993, em11993, dsL]
  · norm_num [world11993, agent11993, scalar11993, tp11993, tm11993, ep11993, em11993, dsL]
  · norm_num [world11993, agent11993, scalar11993, tp11993, tm11993, ep11993, em11993, dsL]
  · norm_num [world11993, agent11993, scalar11993, tp11993, tm11993, ep11993, em11993, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11993, agent11993, tp11993, tm11993, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11993, agent11993, tp11993, tm11993, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11993, agent11993, scalar11993, tp11993, tm11993, ep11993, em11993, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11993, agent11993, tp11993, tm11993, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11993, agent11993, scalar11993, tp11993, tm11993, ep11993, em11993, dsL]

theorem tails11993 :
    exp (-((11993:ℝ)*ep11993)) ≤ scalar11993.upperTail ∧
    exp (-((11993:ℝ)*em11993)) ≤ scalar11993.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11993:ℝ)) (by norm_num [ep11993]) ?_)
      (show bp11993^8 ≤ scalar11993.upperTail by norm_num [bp11993, scalar11993])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11993, bp11993, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11993:ℝ)) (by norm_num [em11993]) ?_)
      (show bm11993^8 ≤ scalar11993.lowerTail by norm_num [bm11993, scalar11993])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11993, bm11993, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11993 :
    agent11993.root+dsL+scalar11993.worldRadius < √(1/100/aL) ∧
    2*(agent11993.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11993, agent11993, scalar11993, tp11993, tm11993, ep11993, em11993, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11993, agent11993, scalar11993, tp11993, tm11993, ep11993, em11993, dsL]

noncomputable def master11993 : MasterCertificate 11993 world11993 agent11993 :=
  master scalar11993 dsL tp11993 tm11993 ep11993 em11993
    (by norm_num [dsL]) (by norm_num [tp11993]) (by norm_num [tm11993])
    (by norm_num [ep11993]) (by norm_num [em11993])
    positive11993 negative11993 tails11993.1 tails11993.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11993.1 tailGuards11993.2

theorem preserves11993 : master11993.toScalarCertificate = scalar11993 := rfl

noncomputable def tp11994 : ℝ := (484746409 / 2000000000)
noncomputable def tm11994 : ℝ := (-((3132334437 / 5000000000)))
noncomputable def ep11994 : ℝ := (2810531034022467 / 5000000000000000000)
noncomputable def em11994 : ℝ := (10823492215559523 / 20000000000000000000)
noncomputable def bp11994 : ℝ := (10763255818394415881 / 25000000000000000000)
noncomputable def bm11994 : ℝ := (5553190398086045673 / 12500000000000000000)

theorem positive11994 :
    Eplus aL (agent11994.root+dsL) scalar11994.worldRadius world11994.frame
      agent11994.frame tp11994 ≤ -ep11994 := by
  apply positive_check (eT := (116666206426677276551 / 100000000000000000000)) (y := (39787017327596009519 / 100000000000000000000)) (u := (14886507507109423021 / 10000000000000000000))
  · norm_num [world11994, agent11994, scalar11994, tp11994, tm11994, ep11994, em11994, dsL]
  · norm_num [world11994, agent11994, scalar11994, tp11994, tm11994, ep11994, em11994, dsL]
  · norm_num [world11994, agent11994, scalar11994, tp11994, tm11994, ep11994, em11994, dsL]
  · norm_num [world11994, agent11994, scalar11994, tp11994, tm11994, ep11994, em11994, dsL]
  · norm_num [world11994, agent11994, scalar11994, tp11994, tm11994, ep11994, em11994, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11994, agent11994, tp11994, tm11994, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11994, agent11994, scalar11994, tp11994, tm11994, ep11994, em11994, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11994, agent11994, tp11994, tm11994, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11994, agent11994, scalar11994, tp11994, tm11994, ep11994, em11994, dsL]

theorem negative11994 :
    Eminus aL (agent11994.root+dsL) scalar11994.worldRadius world11994.frame
      agent11994.frame tm11994 ≤ -em11994 := by
  apply negative_check (lo := (13427517059595106131 / 20000000000000000000)) (hi := (2098049540561735333 / 3125000000000000000))
    (y := (-((9106211430750005383 / 12500000000000000000)))) (u := (4826338851779874671 / 10000000000000000000))
  · norm_num [world11994, agent11994, scalar11994, tp11994, tm11994, ep11994, em11994, dsL]
  · norm_num [world11994, agent11994, scalar11994, tp11994, tm11994, ep11994, em11994, dsL]
  · norm_num [world11994, agent11994, scalar11994, tp11994, tm11994, ep11994, em11994, dsL]
  · norm_num [world11994, agent11994, scalar11994, tp11994, tm11994, ep11994, em11994, dsL]
  · norm_num [world11994, agent11994, scalar11994, tp11994, tm11994, ep11994, em11994, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11994, agent11994, tp11994, tm11994, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11994, agent11994, tp11994, tm11994, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11994, agent11994, scalar11994, tp11994, tm11994, ep11994, em11994, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11994, agent11994, tp11994, tm11994, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11994, agent11994, scalar11994, tp11994, tm11994, ep11994, em11994, dsL]

theorem tails11994 :
    exp (-((11994:ℝ)*ep11994)) ≤ scalar11994.upperTail ∧
    exp (-((11994:ℝ)*em11994)) ≤ scalar11994.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11994:ℝ)) (by norm_num [ep11994]) ?_)
      (show bp11994^8 ≤ scalar11994.upperTail by norm_num [bp11994, scalar11994])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11994, bp11994, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11994:ℝ)) (by norm_num [em11994]) ?_)
      (show bm11994^8 ≤ scalar11994.lowerTail by norm_num [bm11994, scalar11994])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11994, bm11994, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11994 :
    agent11994.root+dsL+scalar11994.worldRadius < √(1/100/aL) ∧
    2*(agent11994.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11994, agent11994, scalar11994, tp11994, tm11994, ep11994, em11994, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11994, agent11994, scalar11994, tp11994, tm11994, ep11994, em11994, dsL]

noncomputable def master11994 : MasterCertificate 11994 world11994 agent11994 :=
  master scalar11994 dsL tp11994 tm11994 ep11994 em11994
    (by norm_num [dsL]) (by norm_num [tp11994]) (by norm_num [tm11994])
    (by norm_num [ep11994]) (by norm_num [em11994])
    positive11994 negative11994 tails11994.1 tails11994.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11994.1 tailGuards11994.2

theorem preserves11994 : master11994.toScalarCertificate = scalar11994 := rfl

noncomputable def tp11995 : ℝ := (605956509 / 2500000000)
noncomputable def tm11995 : ℝ := (-((626487749 / 1000000000)))
noncomputable def ep11995 : ℝ := (28106687756364619 / 50000000000000000000)
noncomputable def em11995 : ℝ := (135299584991121 / 250000000000000000)
noncomputable def bp11995 : ℝ := (8609644035693905811 / 20000000000000000000)
noncomputable def bm11995 : ℝ := (22210468781146403311 / 50000000000000000000)

theorem positive11995 :
    Eplus aL (agent11995.root+dsL) scalar11995.worldRadius world11995.frame
      agent11995.frame tp11995 ≤ -ep11995 := by
  apply positive_check (eT := (58333231847597587509 / 50000000000000000000)) (y := (39787630004095274479 / 100000000000000000000)) (u := (148865987135218802367 / 100000000000000000000))
  · norm_num [world11995, agent11995, scalar11995, tp11995, tm11995, ep11995, em11995, dsL]
  · norm_num [world11995, agent11995, scalar11995, tp11995, tm11995, ep11995, em11995, dsL]
  · norm_num [world11995, agent11995, scalar11995, tp11995, tm11995, ep11995, em11995, dsL]
  · norm_num [world11995, agent11995, scalar11995, tp11995, tm11995, ep11995, em11995, dsL]
  · norm_num [world11995, agent11995, scalar11995, tp11995, tm11995, ep11995, em11995, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11995, agent11995, tp11995, tm11995, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11995, agent11995, scalar11995, tp11995, tm11995, ep11995, em11995, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11995, agent11995, tp11995, tm11995, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11995, agent11995, scalar11995, tp11995, tm11995, ep11995, em11995, dsL]

theorem negative11995 :
    Eminus aL (agent11995.root+dsL) scalar11995.worldRadius world11995.frame
      agent11995.frame tm11995 ≤ -em11995 := by
  apply negative_check (lo := (67137349189508506049 / 100000000000000000000)) (hi := (1342746983790170121 / 2000000000000000000))
    (y := (-((72849298689023339313 / 100000000000000000000)))) (u := (24131789037998297641 / 50000000000000000000))
  · norm_num [world11995, agent11995, scalar11995, tp11995, tm11995, ep11995, em11995, dsL]
  · norm_num [world11995, agent11995, scalar11995, tp11995, tm11995, ep11995, em11995, dsL]
  · norm_num [world11995, agent11995, scalar11995, tp11995, tm11995, ep11995, em11995, dsL]
  · norm_num [world11995, agent11995, scalar11995, tp11995, tm11995, ep11995, em11995, dsL]
  · norm_num [world11995, agent11995, scalar11995, tp11995, tm11995, ep11995, em11995, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11995, agent11995, tp11995, tm11995, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11995, agent11995, tp11995, tm11995, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11995, agent11995, scalar11995, tp11995, tm11995, ep11995, em11995, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11995, agent11995, tp11995, tm11995, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11995, agent11995, scalar11995, tp11995, tm11995, ep11995, em11995, dsL]

theorem tails11995 :
    exp (-((11995:ℝ)*ep11995)) ≤ scalar11995.upperTail ∧
    exp (-((11995:ℝ)*em11995)) ≤ scalar11995.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11995:ℝ)) (by norm_num [ep11995]) ?_)
      (show bp11995^8 ≤ scalar11995.upperTail by norm_num [bp11995, scalar11995])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11995, bp11995, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11995:ℝ)) (by norm_num [em11995]) ?_)
      (show bm11995^8 ≤ scalar11995.lowerTail by norm_num [bm11995, scalar11995])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11995, bm11995, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11995 :
    agent11995.root+dsL+scalar11995.worldRadius < √(1/100/aL) ∧
    2*(agent11995.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11995, agent11995, scalar11995, tp11995, tm11995, ep11995, em11995, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11995, agent11995, scalar11995, tp11995, tm11995, ep11995, em11995, dsL]

noncomputable def master11995 : MasterCertificate 11995 world11995 agent11995 :=
  master scalar11995 dsL tp11995 tm11995 ep11995 em11995
    (by norm_num [dsL]) (by norm_num [tp11995]) (by norm_num [tm11995])
    (by norm_num [ep11995]) (by norm_num [em11995])
    positive11995 negative11995 tails11995.1 tails11995.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11995.1 tailGuards11995.2

theorem preserves11995 : master11995.toScalarCertificate = scalar11995 := rfl

noncomputable def tp11996 : ℝ := (484783997 / 2000000000)
noncomputable def tm11996 : ℝ := (-((1253017167 / 2000000000)))
noncomputable def ep11996 : ℝ := (11243225744830551 / 20000000000000000000)
noncomputable def em11996 : ℝ := (54122205415908703 / 100000000000000000000)
noncomputable def bp11996 : ℝ := (21521709184460736867 / 50000000000000000000)
noncomputable def bm11996 : ℝ := (44416353148231922197 / 100000000000000000000)

theorem positive11996 :
    Eplus aL (agent11996.root+dsL) scalar11996.worldRadius world11996.frame
      agent11996.frame tp11996 ≤ -ep11996 := by
  apply positive_check (eT := (7291670043391082819 / 6250000000000000000)) (y := (9947060623350402479 / 25000000000000000000)) (u := (7443344946313154237 / 5000000000000000000))
  · norm_num [world11996, agent11996, scalar11996, tp11996, tm11996, ep11996, em11996, dsL]
  · norm_num [world11996, agent11996, scalar11996, tp11996, tm11996, ep11996, em11996, dsL]
  · norm_num [world11996, agent11996, scalar11996, tp11996, tm11996, ep11996, em11996, dsL]
  · norm_num [world11996, agent11996, scalar11996, tp11996, tm11996, ep11996, em11996, dsL]
  · norm_num [world11996, agent11996, scalar11996, tp11996, tm11996, ep11996, em11996, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11996, agent11996, tp11996, tm11996, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11996, agent11996, scalar11996, tp11996, tm11996, ep11996, em11996, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11996, agent11996, tp11996, tm11996, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11996, agent11996, scalar11996, tp11996, tm11996, ep11996, em11996, dsL]

theorem negative11996 :
    Eminus aL (agent11996.root+dsL) scalar11996.worldRadius world11996.frame
      agent11996.frame tm11996 ≤ -em11996 := by
  apply negative_check (lo := (16784278542475202603 / 25000000000000000000)) (hi := (67137114169900810413 / 100000000000000000000))
    (y := (-((36424452174832255063 / 50000000000000000000)))) (u := (24131884199328093261 / 50000000000000000000))
  · norm_num [world11996, agent11996, scalar11996, tp11996, tm11996, ep11996, em11996, dsL]
  · norm_num [world11996, agent11996, scalar11996, tp11996, tm11996, ep11996, em11996, dsL]
  · norm_num [world11996, agent11996, scalar11996, tp11996, tm11996, ep11996, em11996, dsL]
  · norm_num [world11996, agent11996, scalar11996, tp11996, tm11996, ep11996, em11996, dsL]
  · norm_num [world11996, agent11996, scalar11996, tp11996, tm11996, ep11996, em11996, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11996, agent11996, tp11996, tm11996, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11996, agent11996, tp11996, tm11996, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11996, agent11996, scalar11996, tp11996, tm11996, ep11996, em11996, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11996, agent11996, tp11996, tm11996, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11996, agent11996, scalar11996, tp11996, tm11996, ep11996, em11996, dsL]

theorem tails11996 :
    exp (-((11996:ℝ)*ep11996)) ≤ scalar11996.upperTail ∧
    exp (-((11996:ℝ)*em11996)) ≤ scalar11996.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11996:ℝ)) (by norm_num [ep11996]) ?_)
      (show bp11996^8 ≤ scalar11996.upperTail by norm_num [bp11996, scalar11996])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11996, bp11996, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11996:ℝ)) (by norm_num [em11996]) ?_)
      (show bm11996^8 ≤ scalar11996.lowerTail by norm_num [bm11996, scalar11996])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11996, bm11996, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11996 :
    agent11996.root+dsL+scalar11996.worldRadius < √(1/100/aL) ∧
    2*(agent11996.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11996, agent11996, scalar11996, tp11996, tm11996, ep11996, em11996, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11996, agent11996, scalar11996, tp11996, tm11996, ep11996, em11996, dsL]

noncomputable def master11996 : MasterCertificate 11996 world11996 agent11996 :=
  master scalar11996 dsL tp11996 tm11996 ep11996 em11996
    (by norm_num [dsL]) (by norm_num [tp11996]) (by norm_num [tm11996])
    (by norm_num [ep11996]) (by norm_num [em11996])
    positive11996 negative11996 tails11996.1 tails11996.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11996.1 tailGuards11996.2

theorem preserves11996 : master11996.toScalarCertificate = scalar11996 := rfl

noncomputable def tp11997 : ℝ := (2424013923 / 10000000000)
noncomputable def tm11997 : ℝ := (-((313264703 / 500000000)))
noncomputable def ep11997 : ℝ := (1756840021428497 / 3125000000000000000)
noncomputable def em11997 : ℝ := (13531143912320741 / 25000000000000000000)
noncomputable def bp11997 : ℝ := (43038617605439559241 / 100000000000000000000)
noncomputable def bm11997 : ℝ := (44411769733948280949 / 100000000000000000000)

theorem positive11997 :
    Eplus aL (agent11997.root+dsL) scalar11997.worldRadius world11997.frame
      agent11997.frame tp11997 ≤ -ep11997 := by
  apply positive_check (eT := (116666977653836878957 / 100000000000000000000)) (y := (9947213836410195489 / 25000000000000000000)) (u := (37216952815795544021 / 25000000000000000000))
  · norm_num [world11997, agent11997, scalar11997, tp11997, tm11997, ep11997, em11997, dsL]
  · norm_num [world11997, agent11997, scalar11997, tp11997, tm11997, ep11997, em11997, dsL]
  · norm_num [world11997, agent11997, scalar11997, tp11997, tm11997, ep11997, em11997, dsL]
  · norm_num [world11997, agent11997, scalar11997, tp11997, tm11997, ep11997, em11997, dsL]
  · norm_num [world11997, agent11997, scalar11997, tp11997, tm11997, ep11997, em11997, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11997, agent11997, tp11997, tm11997, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11997, agent11997, scalar11997, tp11997, tm11997, ep11997, em11997, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11997, agent11997, tp11997, tm11997, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11997, agent11997, scalar11997, tp11997, tm11997, ep11997, em11997, dsL]

theorem negative11997 :
    Eminus aL (agent11997.root+dsL) scalar11997.worldRadius world11997.frame
      agent11997.frame tm11997 ≤ -em11997 := by
  apply negative_check (lo := (67136879594431523483 / 100000000000000000000)) (hi := (16784219898607880871 / 25000000000000000000))
    (y := (-((72848509860754889881 / 100000000000000000000)))) (u := (12065989698561357129 / 25000000000000000000))
  · norm_num [world11997, agent11997, scalar11997, tp11997, tm11997, ep11997, em11997, dsL]
  · norm_num [world11997, agent11997, scalar11997, tp11997, tm11997, ep11997, em11997, dsL]
  · norm_num [world11997, agent11997, scalar11997, tp11997, tm11997, ep11997, em11997, dsL]
  · norm_num [world11997, agent11997, scalar11997, tp11997, tm11997, ep11997, em11997, dsL]
  · norm_num [world11997, agent11997, scalar11997, tp11997, tm11997, ep11997, em11997, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11997, agent11997, tp11997, tm11997, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11997, agent11997, tp11997, tm11997, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11997, agent11997, scalar11997, tp11997, tm11997, ep11997, em11997, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11997, agent11997, tp11997, tm11997, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11997, agent11997, scalar11997, tp11997, tm11997, ep11997, em11997, dsL]

theorem tails11997 :
    exp (-((11997:ℝ)*ep11997)) ≤ scalar11997.upperTail ∧
    exp (-((11997:ℝ)*em11997)) ≤ scalar11997.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11997:ℝ)) (by norm_num [ep11997]) ?_)
      (show bp11997^8 ≤ scalar11997.upperTail by norm_num [bp11997, scalar11997])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11997, bp11997, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11997:ℝ)) (by norm_num [em11997]) ?_)
      (show bm11997^8 ≤ scalar11997.lowerTail by norm_num [bm11997, scalar11997])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11997, bm11997, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11997 :
    agent11997.root+dsL+scalar11997.worldRadius < √(1/100/aL) ∧
    2*(agent11997.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11997, agent11997, scalar11997, tp11997, tm11997, ep11997, em11997, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11997, agent11997, scalar11997, tp11997, tm11997, ep11997, em11997, dsL]

noncomputable def master11997 : MasterCertificate 11997 world11997 agent11997 :=
  master scalar11997 dsL tp11997 tm11997 ep11997 em11997
    (by norm_num [dsL]) (by norm_num [tp11997]) (by norm_num [tm11997])
    (by norm_num [ep11997]) (by norm_num [em11997])
    positive11997 negative11997 tails11997.1 tails11997.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11997.1 tailGuards11997.2

theorem preserves11997 : master11997.toScalarCertificate = scalar11997 := rfl

noncomputable def tp11998 : ℝ := (1212053891 / 5000000000)
noncomputable def tm11998 : ℝ := (-((250620089 / 400000000)))
noncomputable def ep11998 : ℝ := (56221631135541343 / 100000000000000000000)
noncomputable def em11998 : ℝ := (54126944513648291 / 100000000000000000000)
noncomputable def bp11998 : ℝ := (21516909028501376431 / 50000000000000000000)
noncomputable def bm11998 : ℝ := (44407187441253591161 / 100000000000000000000)

theorem positive11998 :
    Eplus aL (agent11998.root+dsL) scalar11998.worldRadius world11998.frame
      agent11998.frame tp11998 ≤ -ep11998 := by
  apply positive_check (eT := (11666723406944387171 / 10000000000000000000)) (y := (9947366825348394999 / 25000000000000000000)) (u := (37217180567776186377 / 25000000000000000000))
  · norm_num [world11998, agent11998, scalar11998, tp11998, tm11998, ep11998, em11998, dsL]
  · norm_num [world11998, agent11998, scalar11998, tp11998, tm11998, ep11998, em11998, dsL]
  · norm_num [world11998, agent11998, scalar11998, tp11998, tm11998, ep11998, em11998, dsL]
  · norm_num [world11998, agent11998, scalar11998, tp11998, tm11998, ep11998, em11998, dsL]
  · norm_num [world11998, agent11998, scalar11998, tp11998, tm11998, ep11998, em11998, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11998, agent11998, tp11998, tm11998, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11998, agent11998, scalar11998, tp11998, tm11998, ep11998, em11998, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11998, agent11998, tp11998, tm11998, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11998, agent11998, scalar11998, tp11998, tm11998, ep11998, em11998, dsL]

theorem negative11998 :
    Eminus aL (agent11998.root+dsL) scalar11998.worldRadius world11998.frame
      agent11998.frame tm11998 ≤ -em11998 := by
  apply negative_check (lo := (16784161301720790239 / 25000000000000000000)) (hi := (67136645206883160957 / 100000000000000000000))
    (y := (-((72848115909548498511 / 100000000000000000000)))) (u := (48264148931067873587 / 100000000000000000000))
  · norm_num [world11998, agent11998, scalar11998, tp11998, tm11998, ep11998, em11998, dsL]
  · norm_num [world11998, agent11998, scalar11998, tp11998, tm11998, ep11998, em11998, dsL]
  · norm_num [world11998, agent11998, scalar11998, tp11998, tm11998, ep11998, em11998, dsL]
  · norm_num [world11998, agent11998, scalar11998, tp11998, tm11998, ep11998, em11998, dsL]
  · norm_num [world11998, agent11998, scalar11998, tp11998, tm11998, ep11998, em11998, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11998, agent11998, tp11998, tm11998, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11998, agent11998, tp11998, tm11998, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11998, agent11998, scalar11998, tp11998, tm11998, ep11998, em11998, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11998, agent11998, tp11998, tm11998, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11998, agent11998, scalar11998, tp11998, tm11998, ep11998, em11998, dsL]

theorem tails11998 :
    exp (-((11998:ℝ)*ep11998)) ≤ scalar11998.upperTail ∧
    exp (-((11998:ℝ)*em11998)) ≤ scalar11998.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11998:ℝ)) (by norm_num [ep11998]) ?_)
      (show bp11998^8 ≤ scalar11998.upperTail by norm_num [bp11998, scalar11998])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11998, bp11998, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11998:ℝ)) (by norm_num [em11998]) ?_)
      (show bm11998^8 ≤ scalar11998.lowerTail by norm_num [bm11998, scalar11998])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11998, bm11998, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11998 :
    agent11998.root+dsL+scalar11998.worldRadius < √(1/100/aL) ∧
    2*(agent11998.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11998, agent11998, scalar11998, tp11998, tm11998, ep11998, em11998, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11998, agent11998, scalar11998, tp11998, tm11998, ep11998, em11998, dsL]

noncomputable def master11998 : MasterCertificate 11998 world11998 agent11998 :=
  master scalar11998 dsL tp11998 tm11998 ep11998 em11998
    (by norm_num [dsL]) (by norm_num [tp11998]) (by norm_num [tm11998])
    (by norm_num [ep11998]) (by norm_num [em11998])
    positive11998 negative11998 tails11998.1 tails11998.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11998.1 tailGuards11998.2

theorem preserves11998 : master11998.toScalarCertificate = scalar11998 := rfl

noncomputable def tp11999 : ℝ := (484840311 / 2000000000)
noncomputable def tm11999 : ℝ := (-((6265710317 / 10000000000)))
noncomputable def ep11999 : ℝ := (56224379126552053 / 100000000000000000000)
noncomputable def em11999 : ℝ := (13532327781411057 / 25000000000000000000)
noncomputable def bp11999 : ℝ := (84041055341409471 / 195312500000000000)
noncomputable def bm11999 : ℝ := (5550325857303725459 / 12500000000000000000)

theorem positive11999 :
    Eplus aL (agent11999.root+dsL) scalar11999.worldRadius world11999.frame
      agent11999.frame tp11999 ≤ -ep11999 := by
  apply positive_check (eT := (29166872472291276787 / 25000000000000000000)) (y := (39790078233434167611 / 100000000000000000000)) (u := (148869631760605691633 / 100000000000000000000))
  · norm_num [world11999, agent11999, scalar11999, tp11999, tm11999, ep11999, em11999, dsL]
  · norm_num [world11999, agent11999, scalar11999, tp11999, tm11999, ep11999, em11999, dsL]
  · norm_num [world11999, agent11999, scalar11999, tp11999, tm11999, ep11999, em11999, dsL]
  · norm_num [world11999, agent11999, scalar11999, tp11999, tm11999, ep11999, em11999, dsL]
  · norm_num [world11999, agent11999, scalar11999, tp11999, tm11999, ep11999, em11999, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11999, agent11999, tp11999, tm11999, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11999, agent11999, scalar11999, tp11999, tm11999, ep11999, em11999, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11999, agent11999, tp11999, tm11999, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11999, agent11999, scalar11999, tp11999, tm11999, ep11999, em11999, dsL]

theorem negative11999 :
    Eminus aL (agent11999.root+dsL) scalar11999.worldRadius world11999.frame
      agent11999.frame tm11999 ≤ -em11999 := by
  apply negative_check (lo := (33568205531383228781 / 50000000000000000000)) (hi := (67136411062766457563 / 100000000000000000000))
    (y := (-((72847721698514414907 / 100000000000000000000)))) (u := (3016521199627717811 / 6250000000000000000))
  · norm_num [world11999, agent11999, scalar11999, tp11999, tm11999, ep11999, em11999, dsL]
  · norm_num [world11999, agent11999, scalar11999, tp11999, tm11999, ep11999, em11999, dsL]
  · norm_num [world11999, agent11999, scalar11999, tp11999, tm11999, ep11999, em11999, dsL]
  · norm_num [world11999, agent11999, scalar11999, tp11999, tm11999, ep11999, em11999, dsL]
  · norm_num [world11999, agent11999, scalar11999, tp11999, tm11999, ep11999, em11999, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11999, agent11999, tp11999, tm11999, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11999, agent11999, tp11999, tm11999, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11999, agent11999, scalar11999, tp11999, tm11999, ep11999, em11999, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11999, agent11999, tp11999, tm11999, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11999, agent11999, scalar11999, tp11999, tm11999, ep11999, em11999, dsL]

theorem tails11999 :
    exp (-((11999:ℝ)*ep11999)) ≤ scalar11999.upperTail ∧
    exp (-((11999:ℝ)*em11999)) ≤ scalar11999.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11999:ℝ)) (by norm_num [ep11999]) ?_)
      (show bp11999^8 ≤ scalar11999.upperTail by norm_num [bp11999, scalar11999])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11999, bp11999, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11999:ℝ)) (by norm_num [em11999]) ?_)
      (show bm11999^8 ≤ scalar11999.lowerTail by norm_num [bm11999, scalar11999])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11999, bm11999, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11999 :
    agent11999.root+dsL+scalar11999.worldRadius < √(1/100/aL) ∧
    2*(agent11999.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11999, agent11999, scalar11999, tp11999, tm11999, ep11999, em11999, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11999, agent11999, scalar11999, tp11999, tm11999, ep11999, em11999, dsL]

noncomputable def master11999 : MasterCertificate 11999 world11999 agent11999 :=
  master scalar11999 dsL tp11999 tm11999 ep11999 em11999
    (by norm_num [dsL]) (by norm_num [tp11999]) (by norm_num [tm11999])
    (by norm_num [ep11999]) (by norm_num [em11999])
    positive11999 negative11999 tails11999.1 tails11999.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11999.1 tailGuards11999.2

theorem preserves11999 : master11999.toScalarCertificate = scalar11999 := rfl

noncomputable def tp12000 : ℝ := (2357731519 / 10000000000)
noncomputable def tm12000 : ℝ := (-((9538849 / 15625000)))
noncomputable def ep12000 : ℝ := (13537268177222163 / 25000000000000000000)
noncomputable def em12000 : ℝ := (418001821660671 / 800000000000000000)
noncomputable def bp12000 : ℝ := (44386443460709493221 / 100000000000000000000)
noncomputable def bm12000 : ℝ := (22834432401510891313 / 50000000000000000000)

theorem positive12000 :
    Eplus aL (agent12000.root+dsL) scalar12000.worldRadius world12000.frame
      agent12000.frame tp12000 ≤ -ep12000 := by
  apply positive_check (eT := (116174962270569772781 / 100000000000000000000)) (y := (19764541575733468537 / 50000000000000000000)) (u := (5939263837625635279 / 4000000000000000000))
  · norm_num [world12000, agent12000, scalar12000, tp12000, tm12000, ep12000, em12000, dsL]
  · norm_num [world12000, agent12000, scalar12000, tp12000, tm12000, ep12000, em12000, dsL]
  · norm_num [world12000, agent12000, scalar12000, tp12000, tm12000, ep12000, em12000, dsL]
  · norm_num [world12000, agent12000, scalar12000, tp12000, tm12000, ep12000, em12000, dsL]
  · norm_num [world12000, agent12000, scalar12000, tp12000, tm12000, ep12000, em12000, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12000, agent12000, tp12000, tm12000, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12000, agent12000, scalar12000, tp12000, tm12000, ep12000, em12000, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12000, agent12000, tp12000, tm12000, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12000, agent12000, scalar12000, tp12000, tm12000, ep12000, em12000, dsL]

theorem negative12000 :
    Eminus aL (agent12000.root+dsL) scalar12000.worldRadius world12000.frame
      agent12000.frame tm12000 ≤ -em12000 := by
  apply negative_check (lo := (67827279762030784663 / 100000000000000000000)) (hi := (8478409970253848083 / 12500000000000000000))
    (y := (-((18339989996869489861 / 25000000000000000000)))) (u := (24008871444162023417 / 50000000000000000000))
  · norm_num [world12000, agent12000, scalar12000, tp12000, tm12000, ep12000, em12000, dsL]
  · norm_num [world12000, agent12000, scalar12000, tp12000, tm12000, ep12000, em12000, dsL]
  · norm_num [world12000, agent12000, scalar12000, tp12000, tm12000, ep12000, em12000, dsL]
  · norm_num [world12000, agent12000, scalar12000, tp12000, tm12000, ep12000, em12000, dsL]
  · norm_num [world12000, agent12000, scalar12000, tp12000, tm12000, ep12000, em12000, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12000, agent12000, tp12000, tm12000, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12000, agent12000, tp12000, tm12000, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12000, agent12000, scalar12000, tp12000, tm12000, ep12000, em12000, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12000, agent12000, tp12000, tm12000, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12000, agent12000, scalar12000, tp12000, tm12000, ep12000, em12000, dsL]

theorem tails12000 :
    exp (-((12000:ℝ)*ep12000)) ≤ scalar12000.upperTail ∧
    exp (-((12000:ℝ)*em12000)) ≤ scalar12000.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12000:ℝ)) (by norm_num [ep12000]) ?_)
      (show bp12000^8 ≤ scalar12000.upperTail by norm_num [bp12000, scalar12000])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12000, bp12000, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12000:ℝ)) (by norm_num [em12000]) ?_)
      (show bm12000^8 ≤ scalar12000.lowerTail by norm_num [bm12000, scalar12000])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12000, bm12000, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12000 :
    agent12000.root+dsL+scalar12000.worldRadius < √(1/100/aL) ∧
    2*(agent12000.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12000, agent12000, scalar12000, tp12000, tm12000, ep12000, em12000, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12000, agent12000, scalar12000, tp12000, tm12000, ep12000, em12000, dsL]

noncomputable def master12000 : MasterCertificate 12000 world12000 agent12000 :=
  master scalar12000 dsL tp12000 tm12000 ep12000 em12000
    (by norm_num [dsL]) (by norm_num [tp12000]) (by norm_num [tm12000])
    (by norm_num [ep12000]) (by norm_num [em12000])
    positive12000 negative12000 tails12000.1 tails12000.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12000.1 tailGuards12000.2

theorem preserves12000 : master12000.toScalarCertificate = scalar12000 := rfl

noncomputable def tp12001 : ℝ := (18420599 / 78125000)
noncomputable def tm12001 : ℝ := (-((305255023 / 500000000)))
noncomputable def ep12001 : ℝ := (846127917782531 / 1562500000000000000)
noncomputable def em12001 : ℝ := (26126472731046837 / 50000000000000000000)
noncomputable def bp12001 : ℝ := (11095341478055745419 / 25000000000000000000)
noncomputable def bm12001 : ℝ := (22832010196326716809 / 50000000000000000000)

theorem positive12001 :
    Eplus aL (agent12001.root+dsL) scalar12001.worldRadius world12001.frame
      agent12001.frame tp12001 ≤ -ep12001 := by
  apply positive_check (eT := (58087656592773649981 / 50000000000000000000)) (y := (9882441068345461729 / 25000000000000000000)) (u := (74241303642387340459 / 50000000000000000000))
  · norm_num [world12001, agent12001, scalar12001, tp12001, tm12001, ep12001, em12001, dsL]
  · norm_num [world12001, agent12001, scalar12001, tp12001, tm12001, ep12001, em12001, dsL]
  · norm_num [world12001, agent12001, scalar12001, tp12001, tm12001, ep12001, em12001, dsL]
  · norm_num [world12001, agent12001, scalar12001, tp12001, tm12001, ep12001, em12001, dsL]
  · norm_num [world12001, agent12001, scalar12001, tp12001, tm12001, ep12001, em12001, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12001, agent12001, tp12001, tm12001, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12001, agent12001, scalar12001, tp12001, tm12001, ep12001, em12001, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12001, agent12001, tp12001, tm12001, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12001, agent12001, scalar12001, tp12001, tm12001, ep12001, em12001, dsL]

theorem negative12001 :
    Eminus aL (agent12001.root+dsL) scalar12001.worldRadius world12001.frame
      agent12001.frame tm12001 ≤ -em12001 := by
  apply negative_check (lo := (33913450486922839071 / 50000000000000000000)) (hi := (67826900973845678143 / 100000000000000000000))
    (y := (-((73359607065424543279 / 100000000000000000000)))) (u := (6002239044228411599 / 12500000000000000000))
  · norm_num [world12001, agent12001, scalar12001, tp12001, tm12001, ep12001, em12001, dsL]
  · norm_num [world12001, agent12001, scalar12001, tp12001, tm12001, ep12001, em12001, dsL]
  · norm_num [world12001, agent12001, scalar12001, tp12001, tm12001, ep12001, em12001, dsL]
  · norm_num [world12001, agent12001, scalar12001, tp12001, tm12001, ep12001, em12001, dsL]
  · norm_num [world12001, agent12001, scalar12001, tp12001, tm12001, ep12001, em12001, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12001, agent12001, tp12001, tm12001, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12001, agent12001, tp12001, tm12001, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12001, agent12001, scalar12001, tp12001, tm12001, ep12001, em12001, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12001, agent12001, tp12001, tm12001, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12001, agent12001, scalar12001, tp12001, tm12001, ep12001, em12001, dsL]

theorem tails12001 :
    exp (-((12001:ℝ)*ep12001)) ≤ scalar12001.upperTail ∧
    exp (-((12001:ℝ)*em12001)) ≤ scalar12001.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12001:ℝ)) (by norm_num [ep12001]) ?_)
      (show bp12001^8 ≤ scalar12001.upperTail by norm_num [bp12001, scalar12001])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12001, bp12001, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12001:ℝ)) (by norm_num [em12001]) ?_)
      (show bm12001^8 ≤ scalar12001.lowerTail by norm_num [bm12001, scalar12001])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12001, bm12001, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12001 :
    agent12001.root+dsL+scalar12001.worldRadius < √(1/100/aL) ∧
    2*(agent12001.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12001, agent12001, scalar12001, tp12001, tm12001, ep12001, em12001, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12001, agent12001, scalar12001, tp12001, tm12001, ep12001, em12001, dsL]

noncomputable def master12001 : MasterCertificate 12001 world12001 agent12001 :=
  master scalar12001 dsL tp12001 tm12001 ep12001 em12001
    (by norm_num [dsL]) (by norm_num [tp12001]) (by norm_num [tm12001])
    (by norm_num [ep12001]) (by norm_num [em12001])
    positive12001 negative12001 tails12001.1 tails12001.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12001.1 tailGuards12001.2

theorem preserves12001 : master12001.toScalarCertificate = scalar12001 := rfl

noncomputable def tp12002 : ℝ := (1178970931 / 5000000000)
noncomputable def tm12002 : ℝ := (-((6105337259 / 10000000000)))
noncomputable def ep12002 : ℝ := (3384706166530183 / 6250000000000000000)
noncomputable def em12002 : ℝ := (52255661270716707 / 100000000000000000000)
noncomputable def bp12002 : ℝ := (44376289999050689363 / 100000000000000000000)
noncomputable def bm12002 : ℝ := (45659177518874845337 / 100000000000000000000)

theorem positive12002 :
    Eplus aL (agent12002.root+dsL) scalar12002.worldRadius world12002.frame
      agent12002.frame tp12002 ≤ -ep12002 := by
  apply positive_check (eT := (116175664410118158933 / 100000000000000000000)) (y := (39530446688946890059 / 100000000000000000000)) (u := (148483620556655532687 / 100000000000000000000))
  · norm_num [world12002, agent12002, scalar12002, tp12002, tm12002, ep12002, em12002, dsL]
  · norm_num [world12002, agent12002, scalar12002, tp12002, tm12002, ep12002, em12002, dsL]
  · norm_num [world12002, agent12002, scalar12002, tp12002, tm12002, ep12002, em12002, dsL]
  · norm_num [world12002, agent12002, scalar12002, tp12002, tm12002, ep12002, em12002, dsL]
  · norm_num [world12002, agent12002, scalar12002, tp12002, tm12002, ep12002, em12002, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12002, agent12002, tp12002, tm12002, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12002, agent12002, scalar12002, tp12002, tm12002, ep12002, em12002, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12002, agent12002, tp12002, tm12002, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12002, agent12002, scalar12002, tp12002, tm12002, ep12002, em12002, dsL]

theorem negative12002 :
    Eminus aL (agent12002.root+dsL) scalar12002.worldRadius world12002.frame
      agent12002.frame tm12002 ≤ -em12002 := by
  apply negative_check (lo := (13565304685060806953 / 20000000000000000000)) (hi := (33913261712652017383 / 50000000000000000000))
    (y := (-((73359252090716585851 / 100000000000000000000)))) (u := (300113017534837301 / 625000000000000000))
  · norm_num [world12002, agent12002, scalar12002, tp12002, tm12002, ep12002, em12002, dsL]
  · norm_num [world12002, agent12002, scalar12002, tp12002, tm12002, ep12002, em12002, dsL]
  · norm_num [world12002, agent12002, scalar12002, tp12002, tm12002, ep12002, em12002, dsL]
  · norm_num [world12002, agent12002, scalar12002, tp12002, tm12002, ep12002, em12002, dsL]
  · norm_num [world12002, agent12002, scalar12002, tp12002, tm12002, ep12002, em12002, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12002, agent12002, tp12002, tm12002, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12002, agent12002, tp12002, tm12002, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12002, agent12002, scalar12002, tp12002, tm12002, ep12002, em12002, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12002, agent12002, tp12002, tm12002, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12002, agent12002, scalar12002, tp12002, tm12002, ep12002, em12002, dsL]

theorem tails12002 :
    exp (-((12002:ℝ)*ep12002)) ≤ scalar12002.upperTail ∧
    exp (-((12002:ℝ)*em12002)) ≤ scalar12002.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12002:ℝ)) (by norm_num [ep12002]) ?_)
      (show bp12002^8 ≤ scalar12002.upperTail by norm_num [bp12002, scalar12002])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12002, bp12002, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12002:ℝ)) (by norm_num [em12002]) ?_)
      (show bm12002^8 ≤ scalar12002.lowerTail by norm_num [bm12002, scalar12002])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12002, bm12002, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12002 :
    agent12002.root+dsL+scalar12002.worldRadius < √(1/100/aL) ∧
    2*(agent12002.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12002, agent12002, scalar12002, tp12002, tm12002, ep12002, em12002, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12002, agent12002, scalar12002, tp12002, tm12002, ep12002, em12002, dsL]

noncomputable def master12002 : MasterCertificate 12002 world12002 agent12002 :=
  master scalar12002 dsL tp12002 tm12002 ep12002 em12002
    (by norm_num [dsL]) (by norm_num [tp12002]) (by norm_num [tm12002])
    (by norm_num [ep12002]) (by norm_num [em12002])
    positive12002 negative12002 tails12002.1 tails12002.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12002.1 tailGuards12002.2

theorem preserves12002 : master12002.toScalarCertificate = scalar12002 := rfl

noncomputable def tp12003 : ℝ := (1179023479 / 5000000000)
noncomputable def tm12003 : ℝ := (-((6105574187 / 10000000000)))
noncomputable def ep12003 : ℝ := (54158409344072367 / 100000000000000000000)
noncomputable def em12003 : ℝ := (6532296986562329 / 12500000000000000000)
noncomputable def bp12003 : ℝ := (22185607575629073589 / 50000000000000000000)
noncomputable def bm12003 : ℝ := (11413583915425857011 / 25000000000000000000)

theorem positive12003 :
    Eplus aL (agent12003.root+dsL) scalar12003.worldRadius world12003.frame
      agent12003.frame tp12003 ≤ -ep12003 := by
  apply positive_check (eT := (116176014976599718377 / 100000000000000000000)) (y := (39531127982316033039 / 100000000000000000000)) (u := (74242316084581334579 / 50000000000000000000))
  · norm_num [world12003, agent12003, scalar12003, tp12003, tm12003, ep12003, em12003, dsL]
  · norm_num [world12003, agent12003, scalar12003, tp12003, tm12003, ep12003, em12003, dsL]
  · norm_num [world12003, agent12003, scalar12003, tp12003, tm12003, ep12003, em12003, dsL]
  · norm_num [world12003, agent12003, scalar12003, tp12003, tm12003, ep12003, em12003, dsL]
  · norm_num [world12003, agent12003, scalar12003, tp12003, tm12003, ep12003, em12003, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12003, agent12003, tp12003, tm12003, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12003, agent12003, scalar12003, tp12003, tm12003, ep12003, em12003, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12003, agent12003, tp12003, tm12003, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12003, agent12003, scalar12003, tp12003, tm12003, ep12003, em12003, dsL]

theorem negative12003 :
    Eminus aL (agent12003.root+dsL) scalar12003.worldRadius world12003.frame
      agent12003.frame tm12003 ≤ -em12003 := by
  apply negative_check (lo := (67826145261766063529 / 100000000000000000000)) (hi := (6782614526176606353 / 10000000000000000000))
    (y := (-((36679449712133515841 / 50000000000000000000)))) (u := (2400912607477017603 / 5000000000000000000))
  · norm_num [world12003, agent12003, scalar12003, tp12003, tm12003, ep12003, em12003, dsL]
  · norm_num [world12003, agent12003, scalar12003, tp12003, tm12003, ep12003, em12003, dsL]
  · norm_num [world12003, agent12003, scalar12003, tp12003, tm12003, ep12003, em12003, dsL]
  · norm_num [world12003, agent12003, scalar12003, tp12003, tm12003, ep12003, em12003, dsL]
  · norm_num [world12003, agent12003, scalar12003, tp12003, tm12003, ep12003, em12003, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12003, agent12003, tp12003, tm12003, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12003, agent12003, tp12003, tm12003, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12003, agent12003, scalar12003, tp12003, tm12003, ep12003, em12003, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12003, agent12003, tp12003, tm12003, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12003, agent12003, scalar12003, tp12003, tm12003, ep12003, em12003, dsL]

theorem tails12003 :
    exp (-((12003:ℝ)*ep12003)) ≤ scalar12003.upperTail ∧
    exp (-((12003:ℝ)*em12003)) ≤ scalar12003.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12003:ℝ)) (by norm_num [ep12003]) ?_)
      (show bp12003^8 ≤ scalar12003.upperTail by norm_num [bp12003, scalar12003])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12003, bp12003, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12003:ℝ)) (by norm_num [em12003]) ?_)
      (show bm12003^8 ≤ scalar12003.lowerTail by norm_num [bm12003, scalar12003])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12003, bm12003, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12003 :
    agent12003.root+dsL+scalar12003.worldRadius < √(1/100/aL) ∧
    2*(agent12003.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12003, agent12003, scalar12003, tp12003, tm12003, ep12003, em12003, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12003, agent12003, scalar12003, tp12003, tm12003, ep12003, em12003, dsL]

noncomputable def master12003 : MasterCertificate 12003 world12003 agent12003 :=
  master scalar12003 dsL tp12003 tm12003 ep12003 em12003
    (by norm_num [dsL]) (by norm_num [tp12003]) (by norm_num [tm12003])
    (by norm_num [ep12003]) (by norm_num [em12003])
    positive12003 negative12003 tails12003.1 tails12003.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12003.1 tailGuards12003.2

theorem preserves12003 : master12003.toScalarCertificate = scalar12003 := rfl

noncomputable def tp12004 : ℝ := (294769 / 1250000)
noncomputable def tm12004 : ℝ := (-((381613173 / 625000000)))
noncomputable def ep12004 : ℝ := (54161518215645109 / 100000000000000000000)
noncomputable def em12004 : ℝ := (26130544415616869 / 50000000000000000000)
noncomputable def bp12004 : ℝ := (22183070871211091191 / 50000000000000000000)
noncomputable def bm12004 : ℝ := (45649495161014221683 / 100000000000000000000)

theorem positive12004 :
    Eplus aL (agent12004.root+dsL) scalar12004.worldRadius world12004.frame
      agent12004.frame tp12004 ≤ -ep12004 := by
  apply positive_check (eT := (116176365180467305071 / 100000000000000000000)) (y := (19765904570389570207 / 50000000000000000000)) (u := (18560705448530722837 / 12500000000000000000))
  · norm_num [world12004, agent12004, scalar12004, tp12004, tm12004, ep12004, em12004, dsL]
  · norm_num [world12004, agent12004, scalar12004, tp12004, tm12004, ep12004, em12004, dsL]
  · norm_num [world12004, agent12004, scalar12004, tp12004, tm12004, ep12004, em12004, dsL]
  · norm_num [world12004, agent12004, scalar12004, tp12004, tm12004, ep12004, em12004, dsL]
  · norm_num [world12004, agent12004, scalar12004, tp12004, tm12004, ep12004, em12004, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12004, agent12004, tp12004, tm12004, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12004, agent12004, scalar12004, tp12004, tm12004, ep12004, em12004, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12004, agent12004, tp12004, tm12004, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12004, agent12004, scalar12004, tp12004, tm12004, ep12004, em12004, dsL]

theorem negative12004 :
    Eminus aL (agent12004.root+dsL) scalar12004.worldRadius world12004.frame
      agent12004.frame tm12004 ≤ -em12004 := by
  apply negative_check (lo := (67825768536145914801 / 100000000000000000000)) (hi := (33912884268072957401 / 50000000000000000000))
    (y := (-((73358545099281633553 / 100000000000000000000)))) (u := (9603684458101339031 / 20000000000000000000))
  · norm_num [world12004, agent12004, scalar12004, tp12004, tm12004, ep12004, em12004, dsL]
  · norm_num [world12004, agent12004, scalar12004, tp12004, tm12004, ep12004, em12004, dsL]
  · norm_num [world12004, agent12004, scalar12004, tp12004, tm12004, ep12004, em12004, dsL]
  · norm_num [world12004, agent12004, scalar12004, tp12004, tm12004, ep12004, em12004, dsL]
  · norm_num [world12004, agent12004, scalar12004, tp12004, tm12004, ep12004, em12004, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12004, agent12004, tp12004, tm12004, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12004, agent12004, tp12004, tm12004, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12004, agent12004, scalar12004, tp12004, tm12004, ep12004, em12004, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12004, agent12004, tp12004, tm12004, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12004, agent12004, scalar12004, tp12004, tm12004, ep12004, em12004, dsL]

theorem tails12004 :
    exp (-((12004:ℝ)*ep12004)) ≤ scalar12004.upperTail ∧
    exp (-((12004:ℝ)*em12004)) ≤ scalar12004.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12004:ℝ)) (by norm_num [ep12004]) ?_)
      (show bp12004^8 ≤ scalar12004.upperTail by norm_num [bp12004, scalar12004])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12004, bp12004, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12004:ℝ)) (by norm_num [em12004]) ?_)
      (show bm12004^8 ≤ scalar12004.lowerTail by norm_num [bm12004, scalar12004])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12004, bm12004, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12004 :
    agent12004.root+dsL+scalar12004.worldRadius < √(1/100/aL) ∧
    2*(agent12004.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12004, agent12004, scalar12004, tp12004, tm12004, ep12004, em12004, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12004, agent12004, scalar12004, tp12004, tm12004, ep12004, em12004, dsL]

noncomputable def master12004 : MasterCertificate 12004 world12004 agent12004 :=
  master scalar12004 dsL tp12004 tm12004 ep12004 em12004
    (by norm_num [dsL]) (by norm_num [tp12004]) (by norm_num [tm12004])
    (by norm_num [ep12004]) (by norm_num [em12004])
    positive12004 negative12004 tails12004.1 tails12004.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12004.1 tailGuards12004.2

theorem preserves12004 : master12004.toScalarCertificate = scalar12004 := rfl

noncomputable def tp12005 : ℝ := (2358256999 / 10000000000)
noncomputable def tm12005 : ℝ := (-((3053023653 / 5000000000)))
noncomputable def ep12005 : ℝ := (5416462546599961 / 10000000000000000000)
noncomputable def em12005 : ℝ := (816621879172243 / 1562500000000000000)
noncomputable def bp12005 : ℝ := (44361069648132198337 / 100000000000000000000)
noncomputable def bm12005 : ℝ := (356598874167275393 / 781250000000000000)

theorem positive12005 :
    Eplus aL (agent12005.root+dsL) scalar12005.worldRadius world12005.frame
      agent12005.frame tp12005 ≤ -ep12005 := by
  apply positive_check (eT := (3630522346969082689 / 3125000000000000000)) (y := (1235390315489086673 / 3125000000000000000)) (u := (5939466188476484667 / 4000000000000000000))
  · norm_num [world12005, agent12005, scalar12005, tp12005, tm12005, ep12005, em12005, dsL]
  · norm_num [world12005, agent12005, scalar12005, tp12005, tm12005, ep12005, em12005, dsL]
  · norm_num [world12005, agent12005, scalar12005, tp12005, tm12005, ep12005, em12005, dsL]
  · norm_num [world12005, agent12005, scalar12005, tp12005, tm12005, ep12005, em12005, dsL]
  · norm_num [world12005, agent12005, scalar12005, tp12005, tm12005, ep12005, em12005, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12005, agent12005, tp12005, tm12005, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12005, agent12005, scalar12005, tp12005, tm12005, ep12005, em12005, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12005, agent12005, tp12005, tm12005, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12005, agent12005, scalar12005, tp12005, tm12005, ep12005, em12005, dsL]

theorem negative12005 :
    Eminus aL (agent12005.root+dsL) scalar12005.worldRadius world12005.frame
      agent12005.frame tm12005 ≤ -em12005 := by
  apply negative_check (lo := (2119543498040900813 / 3125000000000000000)) (hi := (67825391937308826017 / 100000000000000000000))
    (y := (-((3667909569276525513 / 5000000000000000000)))) (u := (4801859213856979693 / 10000000000000000000))
  · norm_num [world12005, agent12005, scalar12005, tp12005, tm12005, ep12005, em12005, dsL]
  · norm_num [world12005, agent12005, scalar12005, tp12005, tm12005, ep12005, em12005, dsL]
  · norm_num [world12005, agent12005, scalar12005, tp12005, tm12005, ep12005, em12005, dsL]
  · norm_num [world12005, agent12005, scalar12005, tp12005, tm12005, ep12005, em12005, dsL]
  · norm_num [world12005, agent12005, scalar12005, tp12005, tm12005, ep12005, em12005, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12005, agent12005, tp12005, tm12005, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12005, agent12005, tp12005, tm12005, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12005, agent12005, scalar12005, tp12005, tm12005, ep12005, em12005, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12005, agent12005, tp12005, tm12005, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12005, agent12005, scalar12005, tp12005, tm12005, ep12005, em12005, dsL]

theorem tails12005 :
    exp (-((12005:ℝ)*ep12005)) ≤ scalar12005.upperTail ∧
    exp (-((12005:ℝ)*em12005)) ≤ scalar12005.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12005:ℝ)) (by norm_num [ep12005]) ?_)
      (show bp12005^8 ≤ scalar12005.upperTail by norm_num [bp12005, scalar12005])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12005, bp12005, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12005:ℝ)) (by norm_num [em12005]) ?_)
      (show bm12005^8 ≤ scalar12005.lowerTail by norm_num [bm12005, scalar12005])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12005, bm12005, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12005 :
    agent12005.root+dsL+scalar12005.worldRadius < √(1/100/aL) ∧
    2*(agent12005.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12005, agent12005, scalar12005, tp12005, tm12005, ep12005, em12005, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12005, agent12005, scalar12005, tp12005, tm12005, ep12005, em12005, dsL]

noncomputable def master12005 : MasterCertificate 12005 world12005 agent12005 :=
  master scalar12005 dsL tp12005 tm12005 ep12005 em12005
    (by norm_num [dsL]) (by norm_num [tp12005]) (by norm_num [tm12005])
    (by norm_num [ep12005]) (by norm_num [em12005])
    positive12005 negative12005 tails12005.1 tails12005.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12005.1 tailGuards12005.2

theorem preserves12005 : master12005.toScalarCertificate = scalar12005 := rfl

noncomputable def tp12006 : ℝ := (2358361989 / 10000000000)
noncomputable def tm12006 : ℝ := (-((6106283603 / 10000000000)))
noncomputable def ep12006 : ℝ := (5416773117323433 / 10000000000000000000)
noncomputable def em12006 : ℝ := (13066627551979397 / 25000000000000000000)
noncomputable def bp12006 : ℝ := (44355998816351627899 / 100000000000000000000)
noncomputable def bm12006 : ℝ := (45639817853354958543 / 100000000000000000000)

theorem positive12006 :
    Eplus aL (agent12006.root+dsL) scalar12006.worldRadius world12006.frame
      agent12006.frame tp12006 ≤ -ep12006 := by
  apply positive_check (eT := (116177064995376158703 / 100000000000000000000)) (y := (1581326871247561273 / 4000000000000000000)) (u := (5939506677096543629 / 4000000000000000000))
  · norm_num [world12006, agent12006, scalar12006, tp12006, tm12006, ep12006, em12006, dsL]
  · norm_num [world12006, agent12006, scalar12006, tp12006, tm12006, ep12006, em12006, dsL]
  · norm_num [world12006, agent12006, scalar12006, tp12006, tm12006, ep12006, em12006, dsL]
  · norm_num [world12006, agent12006, scalar12006, tp12006, tm12006, ep12006, em12006, dsL]
  · norm_num [world12006, agent12006, scalar12006, tp12006, tm12006, ep12006, em12006, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12006, agent12006, tp12006, tm12006, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12006, agent12006, scalar12006, tp12006, tm12006, ep12006, em12006, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12006, agent12006, tp12006, tm12006, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12006, agent12006, scalar12006, tp12006, tm12006, ep12006, em12006, dsL]

theorem negative12006 :
    Eminus aL (agent12006.root+dsL) scalar12006.worldRadius world12006.frame
      agent12006.frame tm12006 ≤ -em12006 := by
  apply negative_check (lo := (13565003263821882413 / 20000000000000000000)) (hi := (33912508159554706033 / 50000000000000000000))
    (y := (-((73357836932565594439 / 100000000000000000000)))) (u := (24009381171097494323 / 50000000000000000000))
  · norm_num [world12006, agent12006, scalar12006, tp12006, tm12006, ep12006, em12006, dsL]
  · norm_num [world12006, agent12006, scalar12006, tp12006, tm12006, ep12006, em12006, dsL]
  · norm_num [world12006, agent12006, scalar12006, tp12006, tm12006, ep12006, em12006, dsL]
  · norm_num [world12006, agent12006, scalar12006, tp12006, tm12006, ep12006, em12006, dsL]
  · norm_num [world12006, agent12006, scalar12006, tp12006, tm12006, ep12006, em12006, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12006, agent12006, tp12006, tm12006, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12006, agent12006, tp12006, tm12006, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12006, agent12006, scalar12006, tp12006, tm12006, ep12006, em12006, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12006, agent12006, tp12006, tm12006, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12006, agent12006, scalar12006, tp12006, tm12006, ep12006, em12006, dsL]

theorem tails12006 :
    exp (-((12006:ℝ)*ep12006)) ≤ scalar12006.upperTail ∧
    exp (-((12006:ℝ)*em12006)) ≤ scalar12006.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12006:ℝ)) (by norm_num [ep12006]) ?_)
      (show bp12006^8 ≤ scalar12006.upperTail by norm_num [bp12006, scalar12006])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12006, bp12006, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12006:ℝ)) (by norm_num [em12006]) ?_)
      (show bm12006^8 ≤ scalar12006.lowerTail by norm_num [bm12006, scalar12006])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12006, bm12006, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12006 :
    agent12006.root+dsL+scalar12006.worldRadius < √(1/100/aL) ∧
    2*(agent12006.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12006, agent12006, scalar12006, tp12006, tm12006, ep12006, em12006, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12006, agent12006, scalar12006, tp12006, tm12006, ep12006, em12006, dsL]

noncomputable def master12006 : MasterCertificate 12006 world12006 agent12006 :=
  master scalar12006 dsL tp12006 tm12006 ep12006 em12006
    (by norm_num [dsL]) (by norm_num [tp12006]) (by norm_num [tm12006])
    (by norm_num [ep12006]) (by norm_num [em12006])
    positive12006 negative12006 tails12006.1 tails12006.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12006.1 tailGuards12006.2

theorem preserves12006 : master12006.toScalarCertificate = scalar12006 := rfl

noncomputable def tp12007 : ℝ := (471693377 / 2000000000)
noncomputable def tm12007 : ℝ := (-((6106519789 / 10000000000)))
noncomputable def ep12007 : ℝ := (54170834408553471 / 100000000000000000000)
noncomputable def em12007 : ℝ := (5226921789154337 / 10000000000000000000)
noncomputable def bp12007 : ℝ := (44350929865291521189 / 100000000000000000000)
noncomputable def bm12007 : ℝ := (45634981562986801651 / 100000000000000000000)

theorem positive12007 :
    Eplus aL (agent12007.root+dsL) scalar12007.worldRadius world12007.frame
      agent12007.frame tp12007 ≤ -ep12007 := by
  apply positive_check (eT := (23235482845941199291 / 20000000000000000000)) (y := (39533852392102369973 / 100000000000000000000)) (u := (5939547102164754953 / 4000000000000000000))
  · norm_num [world12007, agent12007, scalar12007, tp12007, tm12007, ep12007, em12007, dsL]
  · norm_num [world12007, agent12007, scalar12007, tp12007, tm12007, ep12007, em12007, dsL]
  · norm_num [world12007, agent12007, scalar12007, tp12007, tm12007, ep12007, em12007, dsL]
  · norm_num [world12007, agent12007, scalar12007, tp12007, tm12007, ep12007, em12007, dsL]
  · norm_num [world12007, agent12007, scalar12007, tp12007, tm12007, ep12007, em12007, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12007, agent12007, tp12007, tm12007, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12007, agent12007, scalar12007, tp12007, tm12007, ep12007, em12007, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12007, agent12007, tp12007, tm12007, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12007, agent12007, scalar12007, tp12007, tm12007, ep12007, em12007, dsL]

theorem negative12007 :
    Eminus aL (agent12007.root+dsL) scalar12007.worldRadius world12007.frame
      agent12007.frame tm12007 ≤ -em12007 := by
  apply negative_check (lo := (16956160280224358323 / 25000000000000000000)) (hi := (67824641120897433293 / 100000000000000000000))
    (y := (-((73357482287500993193 / 100000000000000000000)))) (u := (24009466319333845841 / 50000000000000000000))
  · norm_num [world12007, agent12007, scalar12007, tp12007, tm12007, ep12007, em12007, dsL]
  · norm_num [world12007, agent12007, scalar12007, tp12007, tm12007, ep12007, em12007, dsL]
  · norm_num [world12007, agent12007, scalar12007, tp12007, tm12007, ep12007, em12007, dsL]
  · norm_num [world12007, agent12007, scalar12007, tp12007, tm12007, ep12007, em12007, dsL]
  · norm_num [world12007, agent12007, scalar12007, tp12007, tm12007, ep12007, em12007, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12007, agent12007, tp12007, tm12007, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12007, agent12007, tp12007, tm12007, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12007, agent12007, scalar12007, tp12007, tm12007, ep12007, em12007, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12007, agent12007, tp12007, tm12007, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12007, agent12007, scalar12007, tp12007, tm12007, ep12007, em12007, dsL]

theorem tails12007 :
    exp (-((12007:ℝ)*ep12007)) ≤ scalar12007.upperTail ∧
    exp (-((12007:ℝ)*em12007)) ≤ scalar12007.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12007:ℝ)) (by norm_num [ep12007]) ?_)
      (show bp12007^8 ≤ scalar12007.upperTail by norm_num [bp12007, scalar12007])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12007, bp12007, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12007:ℝ)) (by norm_num [em12007]) ?_)
      (show bm12007^8 ≤ scalar12007.lowerTail by norm_num [bm12007, scalar12007])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12007, bm12007, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12007 :
    agent12007.root+dsL+scalar12007.worldRadius < √(1/100/aL) ∧
    2*(agent12007.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12007, agent12007, scalar12007, tp12007, tm12007, ep12007, em12007, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12007, agent12007, scalar12007, tp12007, tm12007, ep12007, em12007, dsL]

noncomputable def master12007 : MasterCertificate 12007 world12007 agent12007 :=
  master scalar12007 dsL tp12007 tm12007 ep12007 em12007
    (by norm_num [dsL]) (by norm_num [tp12007]) (by norm_num [tm12007])
    (by norm_num [ep12007]) (by norm_num [em12007])
    positive12007 negative12007 tails12007.1 tails12007.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12007.1 tailGuards12007.2

theorem preserves12007 : master12007.toScalarCertificate = scalar12007 := rfl

noncomputable def tp12008 : ℝ := (1179285827 / 5000000000)
noncomputable def tm12008 : ℝ := (-((1526688969 / 2500000000)))
noncomputable def ep12008 : ℝ := (27086968256920803 / 50000000000000000000)
noncomputable def em12008 : ℝ := (522719245232937 / 1000000000000000000)
noncomputable def bp12008 : ℝ := (2771616368853133477 / 6250000000000000000)
noncomputable def bm12008 : ℝ := (9126029239332338351 / 20000000000000000000)

theorem positive12008 :
    Eplus aL (agent12008.root+dsL) scalar12008.worldRadius world12008.frame
      agent12008.frame tp12008 ≤ -ep12008 := by
  apply positive_check (eT := (23235552512456234267 / 20000000000000000000)) (y := (19767265615140108667 / 50000000000000000000)) (u := (37122421388843309163 / 25000000000000000000))
  · norm_num [world12008, agent12008, scalar12008, tp12008, tm12008, ep12008, em12008, dsL]
  · norm_num [world12008, agent12008, scalar12008, tp12008, tm12008, ep12008, em12008, dsL]
  · norm_num [world12008, agent12008, scalar12008, tp12008, tm12008, ep12008, em12008, dsL]
  · norm_num [world12008, agent12008, scalar12008, tp12008, tm12008, ep12008, em12008, dsL]
  · norm_num [world12008, agent12008, scalar12008, tp12008, tm12008, ep12008, em12008, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12008, agent12008, tp12008, tm12008, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12008, agent12008, scalar12008, tp12008, tm12008, ep12008, em12008, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12008, agent12008, tp12008, tm12008, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12008, agent12008, scalar12008, tp12008, tm12008, ep12008, em12008, dsL]

theorem negative12008 :
    Eminus aL (agent12008.root+dsL) scalar12008.worldRadius world12008.frame
      agent12008.frame tm12008 ≤ -em12008 := by
  apply negative_check (lo := (67824266290914570093 / 100000000000000000000)) (hi := (33912133145457285047 / 50000000000000000000))
    (y := (-((73357127829969569349 / 100000000000000000000)))) (u := (48019102845692594413 / 100000000000000000000))
  · norm_num [world12008, agent12008, scalar12008, tp12008, tm12008, ep12008, em12008, dsL]
  · norm_num [world12008, agent12008, scalar12008, tp12008, tm12008, ep12008, em12008, dsL]
  · norm_num [world12008, agent12008, scalar12008, tp12008, tm12008, ep12008, em12008, dsL]
  · norm_num [world12008, agent12008, scalar12008, tp12008, tm12008, ep12008, em12008, dsL]
  · norm_num [world12008, agent12008, scalar12008, tp12008, tm12008, ep12008, em12008, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12008, agent12008, tp12008, tm12008, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12008, agent12008, tp12008, tm12008, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12008, agent12008, scalar12008, tp12008, tm12008, ep12008, em12008, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12008, agent12008, tp12008, tm12008, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12008, agent12008, scalar12008, tp12008, tm12008, ep12008, em12008, dsL]

theorem tails12008 :
    exp (-((12008:ℝ)*ep12008)) ≤ scalar12008.upperTail ∧
    exp (-((12008:ℝ)*em12008)) ≤ scalar12008.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12008:ℝ)) (by norm_num [ep12008]) ?_)
      (show bp12008^8 ≤ scalar12008.upperTail by norm_num [bp12008, scalar12008])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12008, bp12008, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12008:ℝ)) (by norm_num [em12008]) ?_)
      (show bm12008^8 ≤ scalar12008.lowerTail by norm_num [bm12008, scalar12008])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12008, bm12008, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12008 :
    agent12008.root+dsL+scalar12008.worldRadius < √(1/100/aL) ∧
    2*(agent12008.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12008, agent12008, scalar12008, tp12008, tm12008, ep12008, em12008, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12008, agent12008, scalar12008, tp12008, tm12008, ep12008, em12008, dsL]

noncomputable def master12008 : MasterCertificate 12008 world12008 agent12008 :=
  master scalar12008 dsL tp12008 tm12008 ep12008 em12008
    (by norm_num [dsL]) (by norm_num [tp12008]) (by norm_num [tm12008])
    (by norm_num [ep12008]) (by norm_num [em12008])
    positive12008 negative12008 tails12008.1 tails12008.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12008.1 tailGuards12008.2

theorem preserves12008 : master12008.toScalarCertificate = scalar12008 := rfl

end BstLean.Part281
