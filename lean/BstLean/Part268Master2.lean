import BstLean.Part261Checker
import BstLean.Part268Scalar2
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12400 : ℝ := (2287102071 / 10000000000)
noncomputable def tm12400 : ℝ := (-((5997560123 / 10000000000)))
noncomputable def ep12400 : ℝ := (5054210027809819 / 10000000000000000000)
noncomputable def em12400 : ℝ := (12334812696084143 / 25000000000000000000)
noncomputable def bp12400 : ℝ := (45684891051774742003 / 100000000000000000000)
noncomputable def bm12400 : ℝ := (46544637521165845683 / 100000000000000000000)

theorem positive12400 :
    Eplus aL (agent12400.root+dsL) scalar12400.worldRadius world12400.frame
      agent12400.frame tp12400 ≤ -ep12400 := by
  apply positive_check (eT := (5774769938458978831 / 5000000000000000000)) (y := (37628948448751274927 / 100000000000000000000)) (u := (18210860170689287217 / 12500000000000000000))
  · norm_num [world12400, agent12400, scalar12400, tp12400, tm12400, ep12400, em12400, dsL]
  · norm_num [world12400, agent12400, scalar12400, tp12400, tm12400, ep12400, em12400, dsL]
  · norm_num [world12400, agent12400, scalar12400, tp12400, tm12400, ep12400, em12400, dsL]
  · norm_num [world12400, agent12400, scalar12400, tp12400, tm12400, ep12400, em12400, dsL]
  · norm_num [world12400, agent12400, scalar12400, tp12400, tm12400, ep12400, em12400, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12400, agent12400, tp12400, tm12400, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12400, agent12400, scalar12400, tp12400, tm12400, ep12400, em12400, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12400, agent12400, tp12400, tm12400, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12400, agent12400, scalar12400, tp12400, tm12400, ep12400, em12400, dsL]

theorem negative12400 :
    Eminus aL (agent12400.root+dsL) scalar12400.worldRadius world12400.frame
      agent12400.frame tm12400 ≤ -em12400 := by
  apply negative_check (lo := (68538422758828044831 / 100000000000000000000)) (hi := (2141825711213376401 / 3125000000000000000))
    (y := (-((71705286774328977589 / 100000000000000000000)))) (u := (24409444758879477963 / 50000000000000000000))
  · norm_num [world12400, agent12400, scalar12400, tp12400, tm12400, ep12400, em12400, dsL]
  · norm_num [world12400, agent12400, scalar12400, tp12400, tm12400, ep12400, em12400, dsL]
  · norm_num [world12400, agent12400, scalar12400, tp12400, tm12400, ep12400, em12400, dsL]
  · norm_num [world12400, agent12400, scalar12400, tp12400, tm12400, ep12400, em12400, dsL]
  · norm_num [world12400, agent12400, scalar12400, tp12400, tm12400, ep12400, em12400, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12400, agent12400, tp12400, tm12400, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12400, agent12400, tp12400, tm12400, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12400, agent12400, scalar12400, tp12400, tm12400, ep12400, em12400, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12400, agent12400, tp12400, tm12400, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12400, agent12400, scalar12400, tp12400, tm12400, ep12400, em12400, dsL]

theorem tails12400 :
    exp (-((12400:ℝ)*ep12400)) ≤ scalar12400.upperTail ∧
    exp (-((12400:ℝ)*em12400)) ≤ scalar12400.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12400:ℝ)) (by norm_num [ep12400]) ?_)
      (show bp12400^8 ≤ scalar12400.upperTail by norm_num [bp12400, scalar12400])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12400, bp12400, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12400:ℝ)) (by norm_num [em12400]) ?_)
      (show bm12400^8 ≤ scalar12400.lowerTail by norm_num [bm12400, scalar12400])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12400, bm12400, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12400 :
    agent12400.root+dsL+scalar12400.worldRadius < √(1/100/aL) ∧
    2*(agent12400.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12400, agent12400, scalar12400, tp12400, tm12400, ep12400, em12400, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12400, agent12400, scalar12400, tp12400, tm12400, ep12400, em12400, dsL]

noncomputable def master12400 : MasterCertificate 12400 world12400 agent12400 :=
  master scalar12400 dsL tp12400 tm12400 ep12400 em12400
    (by norm_num [dsL]) (by norm_num [tp12400]) (by norm_num [tm12400])
    (by norm_num [ep12400]) (by norm_num [em12400])
    positive12400 negative12400 tails12400.1 tails12400.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12400.1 tailGuards12400.2

theorem preserves12400 : master12400.toScalarCertificate = scalar12400 := rfl

noncomputable def tp12401 : ℝ := (285899739 / 1250000000)
noncomputable def tm12401 : ℝ := (-((1499441947 / 2500000000)))
noncomputable def ep12401 : ℝ := (25272542008878339 / 50000000000000000000)
noncomputable def em12401 : ℝ := (49341832344424549 / 100000000000000000000)
noncomputable def bp12401 : ℝ := (45679892058748255379 / 100000000000000000000)
noncomputable def bm12401 : ℝ := (1454372017785209377 / 3125000000000000000)

theorem positive12401 :
    Eplus aL (agent12401.root+dsL) scalar12401.worldRadius world12401.frame
      agent12401.frame tp12401 ≤ -ep12401 := by
  apply positive_check (eT := (28873928010477406219 / 25000000000000000000)) (y := (37629852752292829467 / 100000000000000000000)) (u := (145688198823098965263 / 100000000000000000000))
  · norm_num [world12401, agent12401, scalar12401, tp12401, tm12401, ep12401, em12401, dsL]
  · norm_num [world12401, agent12401, scalar12401, tp12401, tm12401, ep12401, em12401, dsL]
  · norm_num [world12401, agent12401, scalar12401, tp12401, tm12401, ep12401, em12401, dsL]
  · norm_num [world12401, agent12401, scalar12401, tp12401, tm12401, ep12401, em12401, dsL]
  · norm_num [world12401, agent12401, scalar12401, tp12401, tm12401, ep12401, em12401, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12401, agent12401, tp12401, tm12401, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12401, agent12401, scalar12401, tp12401, tm12401, ep12401, em12401, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12401, agent12401, tp12401, tm12401, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12401, agent12401, scalar12401, tp12401, tm12401, ep12401, em12401, dsL]

theorem negative12401 :
    Eminus aL (agent12401.root+dsL) scalar12401.worldRadius world12401.frame
      agent12401.frame tm12401 ≤ -em12401 := by
  apply negative_check (lo := (34269061872746225877 / 50000000000000000000)) (hi := (13707624749098490351 / 20000000000000000000))
    (y := (-((35852741358413593307 / 50000000000000000000)))) (u := (1952751754436038127 / 4000000000000000000))
  · norm_num [world12401, agent12401, scalar12401, tp12401, tm12401, ep12401, em12401, dsL]
  · norm_num [world12401, agent12401, scalar12401, tp12401, tm12401, ep12401, em12401, dsL]
  · norm_num [world12401, agent12401, scalar12401, tp12401, tm12401, ep12401, em12401, dsL]
  · norm_num [world12401, agent12401, scalar12401, tp12401, tm12401, ep12401, em12401, dsL]
  · norm_num [world12401, agent12401, scalar12401, tp12401, tm12401, ep12401, em12401, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12401, agent12401, tp12401, tm12401, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12401, agent12401, tp12401, tm12401, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12401, agent12401, scalar12401, tp12401, tm12401, ep12401, em12401, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12401, agent12401, tp12401, tm12401, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12401, agent12401, scalar12401, tp12401, tm12401, ep12401, em12401, dsL]

theorem tails12401 :
    exp (-((12401:ℝ)*ep12401)) ≤ scalar12401.upperTail ∧
    exp (-((12401:ℝ)*em12401)) ≤ scalar12401.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12401:ℝ)) (by norm_num [ep12401]) ?_)
      (show bp12401^8 ≤ scalar12401.upperTail by norm_num [bp12401, scalar12401])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12401, bp12401, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12401:ℝ)) (by norm_num [em12401]) ?_)
      (show bm12401^8 ≤ scalar12401.lowerTail by norm_num [bm12401, scalar12401])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12401, bm12401, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12401 :
    agent12401.root+dsL+scalar12401.worldRadius < √(1/100/aL) ∧
    2*(agent12401.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12401, agent12401, scalar12401, tp12401, tm12401, ep12401, em12401, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12401, agent12401, scalar12401, tp12401, tm12401, ep12401, em12401, dsL]

noncomputable def master12401 : MasterCertificate 12401 world12401 agent12401 :=
  master scalar12401 dsL tp12401 tm12401 ep12401 em12401
    (by norm_num [dsL]) (by norm_num [tp12401]) (by norm_num [tm12401])
    (by norm_num [ep12401]) (by norm_num [em12401])
    positive12401 negative12401 tails12401.1 tails12401.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12401.1 tailGuards12401.2

theorem preserves12401 : master12401.toScalarCertificate = scalar12401 := rfl

noncomputable def tp12402 : ℝ := (2287293731 / 10000000000)
noncomputable def tm12402 : ℝ := (-((599797551 / 1000000000)))
noncomputable def ep12402 : ℝ := (25274033103091127 / 50000000000000000000)
noncomputable def em12402 : ℝ := (24672206228155717 / 50000000000000000000)
noncomputable def bp12402 : ℝ := (22837447185206288117 / 50000000000000000000)
noncomputable def bm12402 : ℝ := (2908448302673720029 / 6250000000000000000)

theorem positive12402 :
    Eplus aL (agent12402.root+dsL) scalar12402.worldRadius world12402.frame
      agent12402.frame tp12402 ≤ -ep12402 := by
  apply positive_check (eT := (115496025186699000241 / 100000000000000000000)) (y := (37630757201124035919 / 100000000000000000000)) (u := (145689516504269293503 / 100000000000000000000))
  · norm_num [world12402, agent12402, scalar12402, tp12402, tm12402, ep12402, em12402, dsL]
  · norm_num [world12402, agent12402, scalar12402, tp12402, tm12402, ep12402, em12402, dsL]
  · norm_num [world12402, agent12402, scalar12402, tp12402, tm12402, ep12402, em12402, dsL]
  · norm_num [world12402, agent12402, scalar12402, tp12402, tm12402, ep12402, em12402, dsL]
  · norm_num [world12402, agent12402, scalar12402, tp12402, tm12402, ep12402, em12402, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12402, agent12402, tp12402, tm12402, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12402, agent12402, scalar12402, tp12402, tm12402, ep12402, em12402, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12402, agent12402, tp12402, tm12402, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12402, agent12402, scalar12402, tp12402, tm12402, ep12402, em12402, dsL]

theorem negative12402 :
    Eminus aL (agent12402.root+dsL) scalar12402.worldRadius world12402.frame
      agent12402.frame tm12402 ≤ -em12402 := by
  apply negative_check (lo := (68537824430072050927 / 100000000000000000000)) (hi := (4283614026879503183 / 6250000000000000000))
    (y := (-((71705680196822241223 / 100000000000000000000)))) (u := (24409348726822221751 / 50000000000000000000))
  · norm_num [world12402, agent12402, scalar12402, tp12402, tm12402, ep12402, em12402, dsL]
  · norm_num [world12402, agent12402, scalar12402, tp12402, tm12402, ep12402, em12402, dsL]
  · norm_num [world12402, agent12402, scalar12402, tp12402, tm12402, ep12402, em12402, dsL]
  · norm_num [world12402, agent12402, scalar12402, tp12402, tm12402, ep12402, em12402, dsL]
  · norm_num [world12402, agent12402, scalar12402, tp12402, tm12402, ep12402, em12402, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12402, agent12402, tp12402, tm12402, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12402, agent12402, tp12402, tm12402, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12402, agent12402, scalar12402, tp12402, tm12402, ep12402, em12402, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12402, agent12402, tp12402, tm12402, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12402, agent12402, scalar12402, tp12402, tm12402, ep12402, em12402, dsL]

theorem tails12402 :
    exp (-((12402:ℝ)*ep12402)) ≤ scalar12402.upperTail ∧
    exp (-((12402:ℝ)*em12402)) ≤ scalar12402.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12402:ℝ)) (by norm_num [ep12402]) ?_)
      (show bp12402^8 ≤ scalar12402.upperTail by norm_num [bp12402, scalar12402])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12402, bp12402, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12402:ℝ)) (by norm_num [em12402]) ?_)
      (show bm12402^8 ≤ scalar12402.lowerTail by norm_num [bm12402, scalar12402])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12402, bm12402, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12402 :
    agent12402.root+dsL+scalar12402.worldRadius < √(1/100/aL) ∧
    2*(agent12402.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12402, agent12402, scalar12402, tp12402, tm12402, ep12402, em12402, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12402, agent12402, scalar12402, tp12402, tm12402, ep12402, em12402, dsL]

noncomputable def master12402 : MasterCertificate 12402 world12402 agent12402 :=
  master scalar12402 dsL tp12402 tm12402 ep12402 em12402
    (by norm_num [dsL]) (by norm_num [tp12402]) (by norm_num [tm12402])
    (by norm_num [ep12402]) (by norm_num [em12402])
    positive12402 negative12402 tails12402.1 tails12402.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12402.1 tailGuards12402.2

theorem preserves12402 : master12402.toScalarCertificate = scalar12402 := rfl

noncomputable def tp12403 : ℝ := (45747791 / 200000000)
noncomputable def tm12403 : ℝ := (-((5998182969 / 10000000000)))
noncomputable def ep12403 : ℝ := (31594404859193 / 62500000000000000)
noncomputable def em12403 : ℝ := (2467349599057473 / 5000000000000000000)
noncomputable def bp12403 : ℝ := (45669897327289519517 / 100000000000000000000)
noncomputable def bm12403 : ℝ := (23265220860434469277 / 50000000000000000000)

theorem positive12403 :
    Eplus aL (agent12403.root+dsL) scalar12403.worldRadius world12403.frame
      agent12403.frame tp12403 ≤ -ep12403 := by
  apply positive_check (eT := (115496338363576222331 / 100000000000000000000)) (y := (37631662086432879319 / 100000000000000000000)) (u := (5827633393330613573 / 4000000000000000000))
  · norm_num [world12403, agent12403, scalar12403, tp12403, tm12403, ep12403, em12403, dsL]
  · norm_num [world12403, agent12403, scalar12403, tp12403, tm12403, ep12403, em12403, dsL]
  · norm_num [world12403, agent12403, scalar12403, tp12403, tm12403, ep12403, em12403, dsL]
  · norm_num [world12403, agent12403, scalar12403, tp12403, tm12403, ep12403, em12403, dsL]
  · norm_num [world12403, agent12403, scalar12403, tp12403, tm12403, ep12403, em12403, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12403, agent12403, tp12403, tm12403, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12403, agent12403, scalar12403, tp12403, tm12403, ep12403, em12403, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12403, agent12403, tp12403, tm12403, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12403, agent12403, scalar12403, tp12403, tm12403, ep12403, em12403, dsL]

theorem negative12403 :
    Eminus aL (agent12403.root+dsL) scalar12403.worldRadius world12403.frame
      agent12403.frame tm12403 ≤ -em12403 := by
  apply negative_check (lo := (34268763096990700571 / 50000000000000000000)) (hi := (68537526193981401143 / 100000000000000000000))
    (y := (-((3585293816114315893 / 5000000000000000000)))) (u := (48818601707841397353 / 100000000000000000000))
  · norm_num [world12403, agent12403, scalar12403, tp12403, tm12403, ep12403, em12403, dsL]
  · norm_num [world12403, agent12403, scalar12403, tp12403, tm12403, ep12403, em12403, dsL]
  · norm_num [world12403, agent12403, scalar12403, tp12403, tm12403, ep12403, em12403, dsL]
  · norm_num [world12403, agent12403, scalar12403, tp12403, tm12403, ep12403, em12403, dsL]
  · norm_num [world12403, agent12403, scalar12403, tp12403, tm12403, ep12403, em12403, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12403, agent12403, tp12403, tm12403, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12403, agent12403, tp12403, tm12403, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12403, agent12403, scalar12403, tp12403, tm12403, ep12403, em12403, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12403, agent12403, tp12403, tm12403, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12403, agent12403, scalar12403, tp12403, tm12403, ep12403, em12403, dsL]

theorem tails12403 :
    exp (-((12403:ℝ)*ep12403)) ≤ scalar12403.upperTail ∧
    exp (-((12403:ℝ)*em12403)) ≤ scalar12403.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12403:ℝ)) (by norm_num [ep12403]) ?_)
      (show bp12403^8 ≤ scalar12403.upperTail by norm_num [bp12403, scalar12403])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12403, bp12403, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12403:ℝ)) (by norm_num [em12403]) ?_)
      (show bm12403^8 ≤ scalar12403.lowerTail by norm_num [bm12403, scalar12403])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12403, bm12403, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12403 :
    agent12403.root+dsL+scalar12403.worldRadius < √(1/100/aL) ∧
    2*(agent12403.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12403, agent12403, scalar12403, tp12403, tm12403, ep12403, em12403, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12403, agent12403, scalar12403, tp12403, tm12403, ep12403, em12403, dsL]

noncomputable def master12403 : MasterCertificate 12403 world12403 agent12403 :=
  master scalar12403 dsL tp12403 tm12403 ep12403 em12403
    (by norm_num [dsL]) (by norm_num [tp12403]) (by norm_num [tm12403])
    (by norm_num [ep12403]) (by norm_num [em12403])
    positive12403 negative12403 tails12403.1 tails12403.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12403.1 tailGuards12403.2

theorem preserves12403 : master12403.toScalarCertificate = scalar12403 := rfl

noncomputable def tp12404 : ℝ := (2287485257 / 10000000000)
noncomputable def tm12404 : ℝ := (-((5998390433 / 10000000000)))
noncomputable def ep12404 : ℝ := (50554027005673773 / 100000000000000000000)
noncomputable def em12404 : ℝ := (12337392336894439 / 25000000000000000000)
noncomputable def bp12404 : ℝ := (713514096024329751 / 1562500000000000000)
noncomputable def bm12404 : ℝ := (5815714042120121321 / 12500000000000000000)

theorem positive12404 :
    Eplus aL (agent12404.root+dsL) scalar12404.worldRadius world12404.frame
      agent12404.frame tp12404 ≤ -ep12404 := by
  apply positive_check (eT := (115496650757806198169 / 100000000000000000000)) (y := (18816282736240780541 / 50000000000000000000)) (u := (14569215098988640973 / 10000000000000000000))
  · norm_num [world12404, agent12404, scalar12404, tp12404, tm12404, ep12404, em12404, dsL]
  · norm_num [world12404, agent12404, scalar12404, tp12404, tm12404, ep12404, em12404, dsL]
  · norm_num [world12404, agent12404, scalar12404, tp12404, tm12404, ep12404, em12404, dsL]
  · norm_num [world12404, agent12404, scalar12404, tp12404, tm12404, ep12404, em12404, dsL]
  · norm_num [world12404, agent12404, scalar12404, tp12404, tm12404, ep12404, em12404, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12404, agent12404, tp12404, tm12404, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12404, agent12404, scalar12404, tp12404, tm12404, ep12404, em12404, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12404, agent12404, tp12404, tm12404, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12404, agent12404, scalar12404, tp12404, tm12404, ep12404, em12404, dsL]

theorem negative12404 :
    Eminus aL (agent12404.root+dsL) scalar12404.worldRadius world12404.frame
      agent12404.frame tm12404 ≤ -em12404 := by
  apply negative_check (lo := (68537227880299160117 / 100000000000000000000)) (hi := (34268613940149580059 / 50000000000000000000))
    (y := (-((35853036463691042693 / 50000000000000000000)))) (u := (48818505728077107869 / 100000000000000000000))
  · norm_num [world12404, agent12404, scalar12404, tp12404, tm12404, ep12404, em12404, dsL]
  · norm_num [world12404, agent12404, scalar12404, tp12404, tm12404, ep12404, em12404, dsL]
  · norm_num [world12404, agent12404, scalar12404, tp12404, tm12404, ep12404, em12404, dsL]
  · norm_num [world12404, agent12404, scalar12404, tp12404, tm12404, ep12404, em12404, dsL]
  · norm_num [world12404, agent12404, scalar12404, tp12404, tm12404, ep12404, em12404, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12404, agent12404, tp12404, tm12404, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12404, agent12404, tp12404, tm12404, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12404, agent12404, scalar12404, tp12404, tm12404, ep12404, em12404, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12404, agent12404, tp12404, tm12404, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12404, agent12404, scalar12404, tp12404, tm12404, ep12404, em12404, dsL]

theorem tails12404 :
    exp (-((12404:ℝ)*ep12404)) ≤ scalar12404.upperTail ∧
    exp (-((12404:ℝ)*em12404)) ≤ scalar12404.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12404:ℝ)) (by norm_num [ep12404]) ?_)
      (show bp12404^8 ≤ scalar12404.upperTail by norm_num [bp12404, scalar12404])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12404, bp12404, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12404:ℝ)) (by norm_num [em12404]) ?_)
      (show bm12404^8 ≤ scalar12404.lowerTail by norm_num [bm12404, scalar12404])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12404, bm12404, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12404 :
    agent12404.root+dsL+scalar12404.worldRadius < √(1/100/aL) ∧
    2*(agent12404.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12404, agent12404, scalar12404, tp12404, tm12404, ep12404, em12404, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12404, agent12404, scalar12404, tp12404, tm12404, ep12404, em12404, dsL]

noncomputable def master12404 : MasterCertificate 12404 world12404 agent12404 :=
  master scalar12404 dsL tp12404 tm12404 ep12404 em12404
    (by norm_num [dsL]) (by norm_num [tp12404]) (by norm_num [tm12404])
    (by norm_num [ep12404]) (by norm_num [em12404])
    positive12404 negative12404 tails12404.1 tails12404.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12404.1 tailGuards12404.2

theorem preserves12404 : master12404.toScalarCertificate = scalar12404 := rfl

noncomputable def tp12405 : ℝ := (142973807 / 625000000)
noncomputable def tm12405 : ℝ := (-((2999298847 / 5000000000)))
noncomputable def ep12405 : ℝ := (12639251171406339 / 25000000000000000000)
noncomputable def em12405 : ℝ := (24676072633086067 / 50000000000000000000)
noncomputable def bp12405 : ℝ := (2853744266764830567 / 6250000000000000000)
noncomputable def bm12405 : ℝ := (465209841784147279 / 1000000000000000000)

theorem positive12405 :
    Eplus aL (agent12405.root+dsL) scalar12405.worldRadius world12405.frame
      agent12405.frame tp12405 ≤ -ep12405 := by
  apply positive_check (eT := (115496962805867076897 / 100000000000000000000)) (y := (18816734236581896551 / 50000000000000000000)) (u := (145693466596943768321 / 100000000000000000000))
  · norm_num [world12405, agent12405, scalar12405, tp12405, tm12405, ep12405, em12405, dsL]
  · norm_num [world12405, agent12405, scalar12405, tp12405, tm12405, ep12405, em12405, dsL]
  · norm_num [world12405, agent12405, scalar12405, tp12405, tm12405, ep12405, em12405, dsL]
  · norm_num [world12405, agent12405, scalar12405, tp12405, tm12405, ep12405, em12405, dsL]
  · norm_num [world12405, agent12405, scalar12405, tp12405, tm12405, ep12405, em12405, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12405, agent12405, tp12405, tm12405, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12405, agent12405, scalar12405, tp12405, tm12405, ep12405, em12405, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12405, agent12405, tp12405, tm12405, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12405, agent12405, scalar12405, tp12405, tm12405, ep12405, em12405, dsL]

theorem negative12405 :
    Eminus aL (agent12405.root+dsL) scalar12405.worldRadius world12405.frame
      agent12405.frame tm12405 ≤ -em12405 := by
  apply negative_check (lo := (68536930386895262023 / 100000000000000000000)) (hi := (8567116298361907753 / 12500000000000000000))
    (y := (-((35853134255296104777 / 50000000000000000000)))) (u := (6102301280921230299 / 12500000000000000000))
  · norm_num [world12405, agent12405, scalar12405, tp12405, tm12405, ep12405, em12405, dsL]
  · norm_num [world12405, agent12405, scalar12405, tp12405, tm12405, ep12405, em12405, dsL]
  · norm_num [world12405, agent12405, scalar12405, tp12405, tm12405, ep12405, em12405, dsL]
  · norm_num [world12405, agent12405, scalar12405, tp12405, tm12405, ep12405, em12405, dsL]
  · norm_num [world12405, agent12405, scalar12405, tp12405, tm12405, ep12405, em12405, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12405, agent12405, tp12405, tm12405, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12405, agent12405, tp12405, tm12405, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12405, agent12405, scalar12405, tp12405, tm12405, ep12405, em12405, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12405, agent12405, tp12405, tm12405, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12405, agent12405, scalar12405, tp12405, tm12405, ep12405, em12405, dsL]

theorem tails12405 :
    exp (-((12405:ℝ)*ep12405)) ≤ scalar12405.upperTail ∧
    exp (-((12405:ℝ)*em12405)) ≤ scalar12405.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12405:ℝ)) (by norm_num [ep12405]) ?_)
      (show bp12405^8 ≤ scalar12405.upperTail by norm_num [bp12405, scalar12405])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12405, bp12405, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12405:ℝ)) (by norm_num [em12405]) ?_)
      (show bm12405^8 ≤ scalar12405.lowerTail by norm_num [bm12405, scalar12405])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12405, bm12405, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12405 :
    agent12405.root+dsL+scalar12405.worldRadius < √(1/100/aL) ∧
    2*(agent12405.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12405, agent12405, scalar12405, tp12405, tm12405, ep12405, em12405, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12405, agent12405, scalar12405, tp12405, tm12405, ep12405, em12405, dsL]

noncomputable def master12405 : MasterCertificate 12405 world12405 agent12405 :=
  master scalar12405 dsL tp12405 tm12405 ep12405 em12405
    (by norm_num [dsL]) (by norm_num [tp12405]) (by norm_num [tm12405])
    (by norm_num [ep12405]) (by norm_num [em12405])
    positive12405 negative12405 tails12405.1 tails12405.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12405.1 tailGuards12405.2

theorem preserves12405 : master12405.toScalarCertificate = scalar12405 := rfl

noncomputable def tp12406 : ℝ := (1143838267 / 5000000000)
noncomputable def tm12406 : ℝ := (-((749850613 / 1250000000)))
noncomputable def ep12406 : ℝ := (50559980963983341 / 100000000000000000000)
noncomputable def em12406 : ℝ := (12338679972882329 / 25000000000000000000)
noncomputable def bp12406 : ℝ := (9130983117899779949 / 20000000000000000000)
noncomputable def bm12406 : ℝ := (46516257133688399669 / 100000000000000000000)

theorem positive12406 :
    Eplus aL (agent12406.root+dsL) scalar12406.worldRadius world12406.frame
      agent12406.frame tp12406 ≤ -ep12406 := by
  apply positive_check (eT := (28874318661505465751 / 25000000000000000000)) (y := (9408592818123009357 / 25000000000000000000)) (u := (29138956384503773539 / 20000000000000000000))
  · norm_num [world12406, agent12406, scalar12406, tp12406, tm12406, ep12406, em12406, dsL]
  · norm_num [world12406, agent12406, scalar12406, tp12406, tm12406, ep12406, em12406, dsL]
  · norm_num [world12406, agent12406, scalar12406, tp12406, tm12406, ep12406, em12406, dsL]
  · norm_num [world12406, agent12406, scalar12406, tp12406, tm12406, ep12406, em12406, dsL]
  · norm_num [world12406, agent12406, scalar12406, tp12406, tm12406, ep12406, em12406, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12406, agent12406, tp12406, tm12406, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12406, agent12406, scalar12406, tp12406, tm12406, ep12406, em12406, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12406, agent12406, tp12406, tm12406, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12406, agent12406, scalar12406, tp12406, tm12406, ep12406, em12406, dsL]

theorem negative12406 :
    Eminus aL (agent12406.root+dsL) scalar12406.worldRadius world12406.frame
      agent12406.frame tm12406 ≤ -em12406 := by
  apply negative_check (lo := (34268316528776864723 / 50000000000000000000)) (hi := (68536633057553729447 / 100000000000000000000))
    (y := (-((71706464278362993667 / 100000000000000000000)))) (u := (2440915733837495857 / 5000000000000000000))
  · norm_num [world12406, agent12406, scalar12406, tp12406, tm12406, ep12406, em12406, dsL]
  · norm_num [world12406, agent12406, scalar12406, tp12406, tm12406, ep12406, em12406, dsL]
  · norm_num [world12406, agent12406, scalar12406, tp12406, tm12406, ep12406, em12406, dsL]
  · norm_num [world12406, agent12406, scalar12406, tp12406, tm12406, ep12406, em12406, dsL]
  · norm_num [world12406, agent12406, scalar12406, tp12406, tm12406, ep12406, em12406, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12406, agent12406, tp12406, tm12406, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12406, agent12406, tp12406, tm12406, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12406, agent12406, scalar12406, tp12406, tm12406, ep12406, em12406, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12406, agent12406, tp12406, tm12406, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12406, agent12406, scalar12406, tp12406, tm12406, ep12406, em12406, dsL]

theorem tails12406 :
    exp (-((12406:ℝ)*ep12406)) ≤ scalar12406.upperTail ∧
    exp (-((12406:ℝ)*em12406)) ≤ scalar12406.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12406:ℝ)) (by norm_num [ep12406]) ?_)
      (show bp12406^8 ≤ scalar12406.upperTail by norm_num [bp12406, scalar12406])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12406, bp12406, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12406:ℝ)) (by norm_num [em12406]) ?_)
      (show bm12406^8 ≤ scalar12406.lowerTail by norm_num [bm12406, scalar12406])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12406, bm12406, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12406 :
    agent12406.root+dsL+scalar12406.worldRadius < √(1/100/aL) ∧
    2*(agent12406.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12406, agent12406, scalar12406, tp12406, tm12406, ep12406, em12406, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12406, agent12406, scalar12406, tp12406, tm12406, ep12406, em12406, dsL]

noncomputable def master12406 : MasterCertificate 12406 world12406 agent12406 :=
  master scalar12406 dsL tp12406 tm12406 ep12406 em12406
    (by norm_num [dsL]) (by norm_num [tp12406]) (by norm_num [tm12406])
    (by norm_num [ep12406]) (by norm_num [em12406])
    positive12406 negative12406 tails12406.1 tails12406.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12406.1 tailGuards12406.2

theorem preserves12406 : master12406.toScalarCertificate = scalar12406 := rfl

noncomputable def tp12407 : ℝ := (457554427 / 2000000000)
noncomputable def tm12407 : ℝ := (-((5999011969 / 10000000000)))
noncomputable def ep12407 : ℝ := (12640738922874433 / 25000000000000000000)
noncomputable def em12407 : ℝ := (9871458613865353 / 20000000000000000000)
noncomputable def bp12407 : ℝ := (22824962107486562779 / 50000000000000000000)
noncomputable def bm12407 : ℝ := (23255765657042009437 / 50000000000000000000)

theorem positive12407 :
    Eplus aL (agent12407.root+dsL) scalar12407.worldRadius world12407.frame
      agent12407.frame tp12407 ≤ -ep12407 := by
  apply positive_check (eT := (7218599147845396269 / 6250000000000000000)) (y := (18817637116769540651 / 50000000000000000000)) (u := (36424024373896687699 / 25000000000000000000))
  · norm_num [world12407, agent12407, scalar12407, tp12407, tm12407, ep12407, em12407, dsL]
  · norm_num [world12407, agent12407, scalar12407, tp12407, tm12407, ep12407, em12407, dsL]
  · norm_num [world12407, agent12407, scalar12407, tp12407, tm12407, ep12407, em12407, dsL]
  · norm_num [world12407, agent12407, scalar12407, tp12407, tm12407, ep12407, em12407, dsL]
  · norm_num [world12407, agent12407, scalar12407, tp12407, tm12407, ep12407, em12407, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12407, agent12407, tp12407, tm12407, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12407, agent12407, scalar12407, tp12407, tm12407, ep12407, em12407, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12407, agent12407, tp12407, tm12407, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12407, agent12407, scalar12407, tp12407, tm12407, ep12407, em12407, dsL]

theorem negative12407 :
    Eminus aL (agent12407.root+dsL) scalar12407.worldRadius world12407.frame
      agent12407.frame tm12407 ≤ -em12407 := by
  apply negative_check (lo := (3426816814903002123 / 5000000000000000000)) (hi := (68536336298060042461 / 100000000000000000000))
    (y := (-((17926664898468022119 / 25000000000000000000)))) (u := (24409109663551595547 / 50000000000000000000))
  · norm_num [world12407, agent12407, scalar12407, tp12407, tm12407, ep12407, em12407, dsL]
  · norm_num [world12407, agent12407, scalar12407, tp12407, tm12407, ep12407, em12407, dsL]
  · norm_num [world12407, agent12407, scalar12407, tp12407, tm12407, ep12407, em12407, dsL]
  · norm_num [world12407, agent12407, scalar12407, tp12407, tm12407, ep12407, em12407, dsL]
  · norm_num [world12407, agent12407, scalar12407, tp12407, tm12407, ep12407, em12407, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12407, agent12407, tp12407, tm12407, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12407, agent12407, tp12407, tm12407, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12407, agent12407, scalar12407, tp12407, tm12407, ep12407, em12407, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12407, agent12407, tp12407, tm12407, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12407, agent12407, scalar12407, tp12407, tm12407, ep12407, em12407, dsL]

theorem tails12407 :
    exp (-((12407:ℝ)*ep12407)) ≤ scalar12407.upperTail ∧
    exp (-((12407:ℝ)*em12407)) ≤ scalar12407.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12407:ℝ)) (by norm_num [ep12407]) ?_)
      (show bp12407^8 ≤ scalar12407.upperTail by norm_num [bp12407, scalar12407])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12407, bp12407, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12407:ℝ)) (by norm_num [em12407]) ?_)
      (show bm12407^8 ≤ scalar12407.lowerTail by norm_num [bm12407, scalar12407])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12407, bm12407, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12407 :
    agent12407.root+dsL+scalar12407.worldRadius < √(1/100/aL) ∧
    2*(agent12407.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12407, agent12407, scalar12407, tp12407, tm12407, ep12407, em12407, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12407, agent12407, scalar12407, tp12407, tm12407, ep12407, em12407, dsL]

noncomputable def master12407 : MasterCertificate 12407 world12407 agent12407 :=
  master scalar12407 dsL tp12407 tm12407 ep12407 em12407
    (by norm_num [dsL]) (by norm_num [tp12407]) (by norm_num [tm12407])
    (by norm_num [ep12407]) (by norm_num [em12407])
    positive12407 negative12407 tails12407.1 tails12407.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12407.1 tailGuards12407.2

theorem preserves12407 : master12407.toScalarCertificate = scalar12407 := rfl

noncomputable def tp12408 : ℝ := (2287867711 / 10000000000)
noncomputable def tm12408 : ℝ := (-((23434449 / 39062500)))
noncomputable def ep12408 : ℝ := (50565929805538757 / 100000000000000000000)
noncomputable def em12408 : ℝ := (12339966414970771 / 25000000000000000000)
noncomputable def bp12408 : ℝ := (114112333702507569 / 250000000000000000)
noncomputable def bm12408 : ℝ := (2906675381188295469 / 6250000000000000000)

theorem positive12408 :
    Eplus aL (agent12408.root+dsL) scalar12408.worldRadius world12408.frame
      agent12408.frame tp12408 ≤ -ep12408 := by
  apply positive_check (eT := (5774894896763847309 / 5000000000000000000)) (y := (9409044271595135129 / 25000000000000000000)) (u := (4553044153840033197 / 3125000000000000000))
  · norm_num [world12408, agent12408, scalar12408, tp12408, tm12408, ep12408, em12408, dsL]
  · norm_num [world12408, agent12408, scalar12408, tp12408, tm12408, ep12408, em12408, dsL]
  · norm_num [world12408, agent12408, scalar12408, tp12408, tm12408, ep12408, em12408, dsL]
  · norm_num [world12408, agent12408, scalar12408, tp12408, tm12408, ep12408, em12408, dsL]
  · norm_num [world12408, agent12408, scalar12408, tp12408, tm12408, ep12408, em12408, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12408, agent12408, tp12408, tm12408, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12408, agent12408, scalar12408, tp12408, tm12408, ep12408, em12408, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12408, agent12408, tp12408, tm12408, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12408, agent12408, scalar12408, tp12408, tm12408, ep12408, em12408, dsL]

theorem negative12408 :
    Eminus aL (agent12408.root+dsL) scalar12408.worldRadius world12408.frame
      agent12408.frame tm12408 ≤ -em12408 := by
  apply negative_check (lo := (68536039871005234369 / 100000000000000000000)) (hi := (6853603987100523437 / 10000000000000000000))
    (y := (-((17926713710259042669 / 25000000000000000000)))) (u := (24409062005503725257 / 50000000000000000000))
  · norm_num [world12408, agent12408, scalar12408, tp12408, tm12408, ep12408, em12408, dsL]
  · norm_num [world12408, agent12408, scalar12408, tp12408, tm12408, ep12408, em12408, dsL]
  · norm_num [world12408, agent12408, scalar12408, tp12408, tm12408, ep12408, em12408, dsL]
  · norm_num [world12408, agent12408, scalar12408, tp12408, tm12408, ep12408, em12408, dsL]
  · norm_num [world12408, agent12408, scalar12408, tp12408, tm12408, ep12408, em12408, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12408, agent12408, tp12408, tm12408, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12408, agent12408, tp12408, tm12408, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12408, agent12408, scalar12408, tp12408, tm12408, ep12408, em12408, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12408, agent12408, tp12408, tm12408, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12408, agent12408, scalar12408, tp12408, tm12408, ep12408, em12408, dsL]

theorem tails12408 :
    exp (-((12408:ℝ)*ep12408)) ≤ scalar12408.upperTail ∧
    exp (-((12408:ℝ)*em12408)) ≤ scalar12408.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12408:ℝ)) (by norm_num [ep12408]) ?_)
      (show bp12408^8 ≤ scalar12408.upperTail by norm_num [bp12408, scalar12408])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12408, bp12408, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12408:ℝ)) (by norm_num [em12408]) ?_)
      (show bm12408^8 ≤ scalar12408.lowerTail by norm_num [bm12408, scalar12408])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12408, bm12408, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12408 :
    agent12408.root+dsL+scalar12408.worldRadius < √(1/100/aL) ∧
    2*(agent12408.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12408, agent12408, scalar12408, tp12408, tm12408, ep12408, em12408, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12408, agent12408, scalar12408, tp12408, tm12408, ep12408, em12408, dsL]

noncomputable def master12408 : MasterCertificate 12408 world12408 agent12408 :=
  master scalar12408 dsL tp12408 tm12408 ep12408 em12408
    (by norm_num [dsL]) (by norm_num [tp12408]) (by norm_num [tm12408])
    (by norm_num [ep12408]) (by norm_num [em12408])
    positive12408 negative12408 tails12408.1 tails12408.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12408.1 tailGuards12408.2

theorem preserves12408 : master12408.toScalarCertificate = scalar12408 := rfl

noncomputable def tp12409 : ℝ := (17874713 / 78125000)
noncomputable def tm12409 : ℝ := (-((599942617 / 1000000000)))
noncomputable def ep12409 : ℝ := (1011378061644889 / 2000000000000000000)
noncomputable def em12409 : ℝ := (49362437723606609 / 100000000000000000000)
noncomputable def bp12409 : ℝ := (5704992943260250987 / 12500000000000000000)
noncomputable def bm12409 : ℝ := (4650208144491737457 / 10000000000000000000)

theorem positive12409 :
    Eplus aL (agent12409.root+dsL) scalar12409.worldRadius world12409.frame
      agent12409.frame tp12409 ≤ -ep12409 := by
  apply positive_check (eT := (28874552342466608957 / 25000000000000000000)) (y := (18818539020998408031 / 50000000000000000000)) (u := (72849362798909429791 / 50000000000000000000))
  · norm_num [world12409, agent12409, scalar12409, tp12409, tm12409, ep12409, em12409, dsL]
  · norm_num [world12409, agent12409, scalar12409, tp12409, tm12409, ep12409, em12409, dsL]
  · norm_num [world12409, agent12409, scalar12409, tp12409, tm12409, ep12409, em12409, dsL]
  · norm_num [world12409, agent12409, scalar12409, tp12409, tm12409, ep12409, em12409, dsL]
  · norm_num [world12409, agent12409, scalar12409, tp12409, tm12409, ep12409, em12409, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12409, agent12409, tp12409, tm12409, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12409, agent12409, scalar12409, tp12409, tm12409, ep12409, em12409, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12409, agent12409, tp12409, tm12409, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12409, agent12409, scalar12409, tp12409, tm12409, ep12409, em12409, dsL]

theorem negative12409 :
    Eminus aL (agent12409.root+dsL) scalar12409.worldRadius world12409.frame
      agent12409.frame tm12409 ≤ -em12409 := by
  apply negative_check (lo := (68535742304534106969 / 100000000000000000000)) (hi := (6853574230453410697 / 10000000000000000000))
    (y := (-((71707049232237210593 / 100000000000000000000)))) (u := (9763605822592419423 / 20000000000000000000))
  · norm_num [world12409, agent12409, scalar12409, tp12409, tm12409, ep12409, em12409, dsL]
  · norm_num [world12409, agent12409, scalar12409, tp12409, tm12409, ep12409, em12409, dsL]
  · norm_num [world12409, agent12409, scalar12409, tp12409, tm12409, ep12409, em12409, dsL]
  · norm_num [world12409, agent12409, scalar12409, tp12409, tm12409, ep12409, em12409, dsL]
  · norm_num [world12409, agent12409, scalar12409, tp12409, tm12409, ep12409, em12409, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12409, agent12409, tp12409, tm12409, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12409, agent12409, tp12409, tm12409, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12409, agent12409, scalar12409, tp12409, tm12409, ep12409, em12409, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12409, agent12409, tp12409, tm12409, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12409, agent12409, scalar12409, tp12409, tm12409, ep12409, em12409, dsL]

theorem tails12409 :
    exp (-((12409:ℝ)*ep12409)) ≤ scalar12409.upperTail ∧
    exp (-((12409:ℝ)*em12409)) ≤ scalar12409.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12409:ℝ)) (by norm_num [ep12409]) ?_)
      (show bp12409^8 ≤ scalar12409.upperTail by norm_num [bp12409, scalar12409])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12409, bp12409, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12409:ℝ)) (by norm_num [em12409]) ?_)
      (show bm12409^8 ≤ scalar12409.lowerTail by norm_num [bm12409, scalar12409])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12409, bm12409, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12409 :
    agent12409.root+dsL+scalar12409.worldRadius < √(1/100/aL) ∧
    2*(agent12409.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12409, agent12409, scalar12409, tp12409, tm12409, ep12409, em12409, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12409, agent12409, scalar12409, tp12409, tm12409, ep12409, em12409, dsL]

noncomputable def master12409 : MasterCertificate 12409 world12409 agent12409 :=
  master scalar12409 dsL tp12409 tm12409 ep12409 em12409
    (by norm_num [dsL]) (by norm_num [tp12409]) (by norm_num [tm12409])
    (by norm_num [ep12409]) (by norm_num [em12409])
    positive12409 negative12409 tails12409.1 tails12409.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12409.1 tailGuards12409.2

theorem preserves12409 : master12409.toScalarCertificate = scalar12409 := rfl

noncomputable def tp12410 : ℝ := (2288135973 / 10000000000)
noncomputable def tm12410 : ℝ := (-((2999933059 / 5000000000)))
noncomputable def ep12410 : ℝ := (25286681413165709 / 50000000000000000000)
noncomputable def em12410 : ℝ := (4936662633283093 / 10000000000000000000)
noncomputable def bp12410 : ℝ := (45633901541157389143 / 100000000000000000000)
noncomputable def bm12410 : ℝ := (46496190987928134481 / 100000000000000000000)

theorem positive12410 :
    Eplus aL (agent12410.root+dsL) scalar12410.worldRadius world12410.frame
      agent12410.frame tp12410 ≤ -ep12410 := by
  apply positive_check (eT := (115499082022015538457 / 100000000000000000000)) (y := (9409310590087456283 / 25000000000000000000)) (u := (72849482503880907153 / 50000000000000000000))
  · norm_num [world12410, agent12410, scalar12410, tp12410, tm12410, ep12410, em12410, dsL]
  · norm_num [world12410, agent12410, scalar12410, tp12410, tm12410, ep12410, em12410, dsL]
  · norm_num [world12410, agent12410, scalar12410, tp12410, tm12410, ep12410, em12410, dsL]
  · norm_num [world12410, agent12410, scalar12410, tp12410, tm12410, ep12410, em12410, dsL]
  · norm_num [world12410, agent12410, scalar12410, tp12410, tm12410, ep12410, em12410, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12410, agent12410, tp12410, tm12410, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12410, agent12410, scalar12410, tp12410, tm12410, ep12410, em12410, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12410, agent12410, tp12410, tm12410, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12410, agent12410, scalar12410, tp12410, tm12410, ep12410, em12410, dsL]

theorem negative12410 :
    Eminus aL (agent12410.root+dsL) scalar12410.worldRadius world12410.frame
      agent12410.frame tm12410 ≤ -em12410 := by
  apply negative_check (lo := (13706888055485502629 / 20000000000000000000)) (hi := (34267220138713756573 / 50000000000000000000))
    (y := (-((35852646469316466551 / 50000000000000000000)))) (u := (24409443254207155549 / 50000000000000000000))
  · norm_num [world12410, agent12410, scalar12410, tp12410, tm12410, ep12410, em12410, dsL]
  · norm_num [world12410, agent12410, scalar12410, tp12410, tm12410, ep12410, em12410, dsL]
  · norm_num [world12410, agent12410, scalar12410, tp12410, tm12410, ep12410, em12410, dsL]
  · norm_num [world12410, agent12410, scalar12410, tp12410, tm12410, ep12410, em12410, dsL]
  · norm_num [world12410, agent12410, scalar12410, tp12410, tm12410, ep12410, em12410, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12410, agent12410, tp12410, tm12410, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12410, agent12410, tp12410, tm12410, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12410, agent12410, scalar12410, tp12410, tm12410, ep12410, em12410, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12410, agent12410, tp12410, tm12410, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12410, agent12410, scalar12410, tp12410, tm12410, ep12410, em12410, dsL]

theorem tails12410 :
    exp (-((12410:ℝ)*ep12410)) ≤ scalar12410.upperTail ∧
    exp (-((12410:ℝ)*em12410)) ≤ scalar12410.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12410:ℝ)) (by norm_num [ep12410]) ?_)
      (show bp12410^8 ≤ scalar12410.upperTail by norm_num [bp12410, scalar12410])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12410, bp12410, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12410:ℝ)) (by norm_num [em12410]) ?_)
      (show bm12410^8 ≤ scalar12410.lowerTail by norm_num [bm12410, scalar12410])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12410, bm12410, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12410 :
    agent12410.root+dsL+scalar12410.worldRadius < √(1/100/aL) ∧
    2*(agent12410.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12410, agent12410, scalar12410, tp12410, tm12410, ep12410, em12410, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12410, agent12410, scalar12410, tp12410, tm12410, ep12410, em12410, dsL]

noncomputable def master12410 : MasterCertificate 12410 world12410 agent12410 :=
  master scalar12410 dsL tp12410 tm12410 ep12410 em12410
    (by norm_num [dsL]) (by norm_num [tp12410]) (by norm_num [tm12410])
    (by norm_num [ep12410]) (by norm_num [em12410])
    positive12410 negative12410 tails12410.1 tails12410.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12410.1 tailGuards12410.2

theorem preserves12410 : master12410.toScalarCertificate = scalar12410 := rfl

noncomputable def tp12411 : ℝ := (1144115851 / 5000000000)
noncomputable def tm12411 : ℝ := (-((1500018421 / 2500000000)))
noncomputable def ep12411 : ℝ := (6322042203072291 / 12500000000000000000)
noncomputable def em12411 : ℝ := (49369200496924733 / 100000000000000000000)
noncomputable def bp12411 : ℝ := (22814455486037205913 / 50000000000000000000)
noncomputable def bm12411 : ℝ := (9298293041096392543 / 20000000000000000000)

theorem positive12411 :
    Eplus aL (agent12411.root+dsL) scalar12411.worldRadius world12411.frame
      agent12411.frame tp12411 ≤ -ep12411 := by
  apply positive_check (eT := (11549939478947241279 / 10000000000000000000)) (y := (9409535294490788979 / 25000000000000000000)) (u := (145700274581607076099 / 100000000000000000000))
  · norm_num [world12411, agent12411, scalar12411, tp12411, tm12411, ep12411, em12411, dsL]
  · norm_num [world12411, agent12411, scalar12411, tp12411, tm12411, ep12411, em12411, dsL]
  · norm_num [world12411, agent12411, scalar12411, tp12411, tm12411, ep12411, em12411, dsL]
  · norm_num [world12411, agent12411, scalar12411, tp12411, tm12411, ep12411, em12411, dsL]
  · norm_num [world12411, agent12411, scalar12411, tp12411, tm12411, ep12411, em12411, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12411, agent12411, tp12411, tm12411, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12411, agent12411, scalar12411, tp12411, tm12411, ep12411, em12411, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12411, agent12411, tp12411, tm12411, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12411, agent12411, scalar12411, tp12411, tm12411, ep12411, em12411, dsL]

theorem negative12411 :
    Eminus aL (agent12411.root+dsL) scalar12411.worldRadius world12411.frame
      agent12411.frame tm12411 ≤ -em12411 := by
  apply negative_check (lo := (34267070579593517341 / 50000000000000000000)) (hi := (68534141159187034683 / 100000000000000000000))
    (y := (-((71705479983169528871 / 100000000000000000000)))) (u := (12204698798859917053 / 25000000000000000000))
  · norm_num [world12411, agent12411, scalar12411, tp12411, tm12411, ep12411, em12411, dsL]
  · norm_num [world12411, agent12411, scalar12411, tp12411, tm12411, ep12411, em12411, dsL]
  · norm_num [world12411, agent12411, scalar12411, tp12411, tm12411, ep12411, em12411, dsL]
  · norm_num [world12411, agent12411, scalar12411, tp12411, tm12411, ep12411, em12411, dsL]
  · norm_num [world12411, agent12411, scalar12411, tp12411, tm12411, ep12411, em12411, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12411, agent12411, tp12411, tm12411, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12411, agent12411, tp12411, tm12411, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12411, agent12411, scalar12411, tp12411, tm12411, ep12411, em12411, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12411, agent12411, tp12411, tm12411, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12411, agent12411, scalar12411, tp12411, tm12411, ep12411, em12411, dsL]

theorem tails12411 :
    exp (-((12411:ℝ)*ep12411)) ≤ scalar12411.upperTail ∧
    exp (-((12411:ℝ)*em12411)) ≤ scalar12411.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12411:ℝ)) (by norm_num [ep12411]) ?_)
      (show bp12411^8 ≤ scalar12411.upperTail by norm_num [bp12411, scalar12411])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12411, bp12411, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12411:ℝ)) (by norm_num [em12411]) ?_)
      (show bm12411^8 ≤ scalar12411.lowerTail by norm_num [bm12411, scalar12411])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12411, bm12411, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12411 :
    agent12411.root+dsL+scalar12411.worldRadius < √(1/100/aL) ∧
    2*(agent12411.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12411, agent12411, scalar12411, tp12411, tm12411, ep12411, em12411, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12411, agent12411, scalar12411, tp12411, tm12411, ep12411, em12411, dsL]

noncomputable def master12411 : MasterCertificate 12411 world12411 agent12411 :=
  master scalar12411 dsL tp12411 tm12411 ep12411 em12411
    (by norm_num [dsL]) (by norm_num [tp12411]) (by norm_num [tm12411])
    (by norm_num [ep12411]) (by norm_num [em12411])
    positive12411 negative12411 tails12411.1 tails12411.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12411.1 tailGuards12411.2

theorem preserves12411 : master12411.toScalarCertificate = scalar12411 := rfl

noncomputable def tp12412 : ℝ := (2288327333 / 10000000000)
noncomputable def tm12412 : ℝ := (-((3000140571 / 5000000000)))
noncomputable def ep12412 : ℝ := (25289655275888459 / 50000000000000000000)
noncomputable def em12412 : ℝ := (24685886467186787 / 50000000000000000000)
noncomputable def bp12412 : ℝ := (22811960966945663149 / 50000000000000000000)
noncomputable def bm12412 : ℝ := (23243370424761182927 / 50000000000000000000)

theorem positive12412 :
    Eplus aL (agent12412.root+dsL) scalar12412.worldRadius world12412.frame
      agent12412.frame tp12412 ≤ -ep12412 := by
  apply positive_check (eT := (57749853438098311483 / 50000000000000000000)) (y := (37639038693040797967 / 100000000000000000000)) (u := (9106348891837996919 / 6250000000000000000))
  · norm_num [world12412, agent12412, scalar12412, tp12412, tm12412, ep12412, em12412, dsL]
  · norm_num [world12412, agent12412, scalar12412, tp12412, tm12412, ep12412, em12412, dsL]
  · norm_num [world12412, agent12412, scalar12412, tp12412, tm12412, ep12412, em12412, dsL]
  · norm_num [world12412, agent12412, scalar12412, tp12412, tm12412, ep12412, em12412, dsL]
  · norm_num [world12412, agent12412, scalar12412, tp12412, tm12412, ep12412, em12412, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12412, agent12412, tp12412, tm12412, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12412, agent12412, scalar12412, tp12412, tm12412, ep12412, em12412, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12412, agent12412, tp12412, tm12412, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12412, agent12412, scalar12412, tp12412, tm12412, ep12412, em12412, dsL]

theorem negative12412 :
    Eminus aL (agent12412.root+dsL) scalar12412.worldRadius world12412.frame
      agent12412.frame tm12412 ≤ -em12412 := by
  apply negative_check (lo := (34266921225589085763 / 50000000000000000000)) (hi := (68533842451178171527 / 100000000000000000000))
    (y := (-((17926416630035136637 / 25000000000000000000)))) (u := (1525584504075711197 / 3125000000000000000))
  · norm_num [world12412, agent12412, scalar12412, tp12412, tm12412, ep12412, em12412, dsL]
  · norm_num [world12412, agent12412, scalar12412, tp12412, tm12412, ep12412, em12412, dsL]
  · norm_num [world12412, agent12412, scalar12412, tp12412, tm12412, ep12412, em12412, dsL]
  · norm_num [world12412, agent12412, scalar12412, tp12412, tm12412, ep12412, em12412, dsL]
  · norm_num [world12412, agent12412, scalar12412, tp12412, tm12412, ep12412, em12412, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12412, agent12412, tp12412, tm12412, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12412, agent12412, tp12412, tm12412, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12412, agent12412, scalar12412, tp12412, tm12412, ep12412, em12412, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12412, agent12412, tp12412, tm12412, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12412, agent12412, scalar12412, tp12412, tm12412, ep12412, em12412, dsL]

theorem tails12412 :
    exp (-((12412:ℝ)*ep12412)) ≤ scalar12412.upperTail ∧
    exp (-((12412:ℝ)*em12412)) ≤ scalar12412.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12412:ℝ)) (by norm_num [ep12412]) ?_)
      (show bp12412^8 ≤ scalar12412.upperTail by norm_num [bp12412, scalar12412])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12412, bp12412, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12412:ℝ)) (by norm_num [em12412]) ?_)
      (show bm12412^8 ≤ scalar12412.lowerTail by norm_num [bm12412, scalar12412])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12412, bm12412, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12412 :
    agent12412.root+dsL+scalar12412.worldRadius < √(1/100/aL) ∧
    2*(agent12412.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12412, agent12412, scalar12412, tp12412, tm12412, ep12412, em12412, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12412, agent12412, scalar12412, tp12412, tm12412, ep12412, em12412, dsL]

noncomputable def master12412 : MasterCertificate 12412 world12412 agent12412 :=
  master scalar12412 dsL tp12412 tm12412 ep12412 em12412
    (by norm_num [dsL]) (by norm_num [tp12412]) (by norm_num [tm12412])
    (by norm_num [ep12412]) (by norm_num [em12412])
    positive12412 negative12412 tails12412.1 tails12412.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12412.1 tailGuards12412.2

theorem preserves12412 : master12412.toScalarCertificate = scalar12412 := rfl

noncomputable def tp12413 : ℝ := (572105731 / 2500000000)
noncomputable def tm12413 : ℝ := (-((1500122107 / 2500000000)))
noncomputable def ep12413 : ℝ := (3161392650541253 / 6250000000000000000)
noncomputable def em12413 : ℝ := (49374344367919777 / 100000000000000000000)
noncomputable def bp12413 : ℝ := (2851183366234925977 / 6250000000000000000)
noncomputable def bm12413 : ℝ := (23241008699376028357 / 50000000000000000000)

theorem positive12413 :
    Eplus aL (agent12413.root+dsL) scalar12413.worldRadius world12413.frame
      agent12413.frame tp12413 ≤ -ep12413 := by
  apply positive_check (eT := (115500018704071594519 / 100000000000000000000)) (y := (4704991997991179489 / 12500000000000000000)) (u := (145702889642295715551 / 100000000000000000000))
  · norm_num [world12413, agent12413, scalar12413, tp12413, tm12413, ep12413, em12413, dsL]
  · norm_num [world12413, agent12413, scalar12413, tp12413, tm12413, ep12413, em12413, dsL]
  · norm_num [world12413, agent12413, scalar12413, tp12413, tm12413, ep12413, em12413, dsL]
  · norm_num [world12413, agent12413, scalar12413, tp12413, tm12413, ep12413, em12413, dsL]
  · norm_num [world12413, agent12413, scalar12413, tp12413, tm12413, ep12413, em12413, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12413, agent12413, tp12413, tm12413, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12413, agent12413, scalar12413, tp12413, tm12413, ep12413, em12413, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12413, agent12413, tp12413, tm12413, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12413, agent12413, scalar12413, tp12413, tm12413, ep12413, em12413, dsL]

theorem negative12413 :
    Eminus aL (agent12413.root+dsL) scalar12413.worldRadius world12413.frame
      agent12413.frame tm12413 ≤ -em12413 := by
  apply negative_check (lo := (13706708885909192483 / 20000000000000000000)) (hi := (4283346526846622651 / 6250000000000000000))
    (y := (-((71705852464956315511 / 100000000000000000000)))) (u := (9763722670931539727 / 20000000000000000000))
  · norm_num [world12413, agent12413, scalar12413, tp12413, tm12413, ep12413, em12413, dsL]
  · norm_num [world12413, agent12413, scalar12413, tp12413, tm12413, ep12413, em12413, dsL]
  · norm_num [world12413, agent12413, scalar12413, tp12413, tm12413, ep12413, em12413, dsL]
  · norm_num [world12413, agent12413, scalar12413, tp12413, tm12413, ep12413, em12413, dsL]
  · norm_num [world12413, agent12413, scalar12413, tp12413, tm12413, ep12413, em12413, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12413, agent12413, tp12413, tm12413, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12413, agent12413, tp12413, tm12413, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12413, agent12413, scalar12413, tp12413, tm12413, ep12413, em12413, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12413, agent12413, tp12413, tm12413, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12413, agent12413, scalar12413, tp12413, tm12413, ep12413, em12413, dsL]

theorem tails12413 :
    exp (-((12413:ℝ)*ep12413)) ≤ scalar12413.upperTail ∧
    exp (-((12413:ℝ)*em12413)) ≤ scalar12413.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12413:ℝ)) (by norm_num [ep12413]) ?_)
      (show bp12413^8 ≤ scalar12413.upperTail by norm_num [bp12413, scalar12413])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12413, bp12413, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12413:ℝ)) (by norm_num [em12413]) ?_)
      (show bm12413^8 ≤ scalar12413.lowerTail by norm_num [bm12413, scalar12413])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12413, bm12413, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12413 :
    agent12413.root+dsL+scalar12413.worldRadius < √(1/100/aL) ∧
    2*(agent12413.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12413, agent12413, scalar12413, tp12413, tm12413, ep12413, em12413, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12413, agent12413, scalar12413, tp12413, tm12413, ep12413, em12413, dsL]

noncomputable def master12413 : MasterCertificate 12413 world12413 agent12413 :=
  master scalar12413 dsL tp12413 tm12413 ep12413 em12413
    (by norm_num [dsL]) (by norm_num [tp12413]) (by norm_num [tm12413])
    (by norm_num [ep12413]) (by norm_num [em12413])
    positive12413 negative12413 tails12413.1 tails12413.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12413.1 tailGuards12413.2

theorem preserves12413 : master12413.toScalarCertificate = scalar12413 := rfl

noncomputable def tp12414 : ℝ := (2288518457 / 10000000000)
noncomputable def tm12414 : ℝ := (-((1500173929 / 2500000000)))
noncomputable def ep12414 : ℝ := (12646313098656823 / 25000000000000000000)
noncomputable def em12414 : ℝ := (49376914075057057 / 100000000000000000000)
noncomputable def bp12414 : ℝ := (22806973658169781361 / 50000000000000000000)
noncomputable def bm12414 : ℝ := (46477295374247424889 / 100000000000000000000)

theorem positive12414 :
    Eplus aL (agent12414.root+dsL) scalar12414.worldRadius world12414.frame
      agent12414.frame tp12414 ≤ -ep12414 := by
  apply positive_check (eT := (115500330142186189767 / 100000000000000000000)) (y := (37640832678298696851 / 100000000000000000000)) (u := (72852098078880352523 / 50000000000000000000))
  · norm_num [world12414, agent12414, scalar12414, tp12414, tm12414, ep12414, em12414, dsL]
  · norm_num [world12414, agent12414, scalar12414, tp12414, tm12414, ep12414, em12414, dsL]
  · norm_num [world12414, agent12414, scalar12414, tp12414, tm12414, ep12414, em12414, dsL]
  · norm_num [world12414, agent12414, scalar12414, tp12414, tm12414, ep12414, em12414, dsL]
  · norm_num [world12414, agent12414, scalar12414, tp12414, tm12414, ep12414, em12414, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12414, agent12414, tp12414, tm12414, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12414, agent12414, scalar12414, tp12414, tm12414, ep12414, em12414, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12414, agent12414, tp12414, tm12414, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12414, agent12414, scalar12414, tp12414, tm12414, ep12414, em12414, dsL]

theorem negative12414 :
    Eminus aL (agent12414.root+dsL) scalar12414.worldRadius world12414.frame
      agent12414.frame tm12414 ≤ -em12414 := by
  apply negative_check (lo := (17133311585845604463 / 25000000000000000000)) (hi := (68533246343382417853 / 100000000000000000000))
    (y := (-((3585301949150037333 / 5000000000000000000)))) (u := (48818522299219668561 / 100000000000000000000))
  · norm_num [world12414, agent12414, scalar12414, tp12414, tm12414, ep12414, em12414, dsL]
  · norm_num [world12414, agent12414, scalar12414, tp12414, tm12414, ep12414, em12414, dsL]
  · norm_num [world12414, agent12414, scalar12414, tp12414, tm12414, ep12414, em12414, dsL]
  · norm_num [world12414, agent12414, scalar12414, tp12414, tm12414, ep12414, em12414, dsL]
  · norm_num [world12414, agent12414, scalar12414, tp12414, tm12414, ep12414, em12414, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12414, agent12414, tp12414, tm12414, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12414, agent12414, tp12414, tm12414, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12414, agent12414, scalar12414, tp12414, tm12414, ep12414, em12414, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12414, agent12414, tp12414, tm12414, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12414, agent12414, scalar12414, tp12414, tm12414, ep12414, em12414, dsL]

theorem tails12414 :
    exp (-((12414:ℝ)*ep12414)) ≤ scalar12414.upperTail ∧
    exp (-((12414:ℝ)*em12414)) ≤ scalar12414.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12414:ℝ)) (by norm_num [ep12414]) ?_)
      (show bp12414^8 ≤ scalar12414.upperTail by norm_num [bp12414, scalar12414])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12414, bp12414, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12414:ℝ)) (by norm_num [em12414]) ?_)
      (show bm12414^8 ≤ scalar12414.lowerTail by norm_num [bm12414, scalar12414])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12414, bm12414, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12414 :
    agent12414.root+dsL+scalar12414.worldRadius < √(1/100/aL) ∧
    2*(agent12414.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12414, agent12414, scalar12414, tp12414, tm12414, ep12414, em12414, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12414, agent12414, scalar12414, tp12414, tm12414, ep12414, em12414, dsL]

noncomputable def master12414 : MasterCertificate 12414 world12414 agent12414 :=
  master scalar12414 dsL tp12414 tm12414 ep12414 em12414
    (by norm_num [dsL]) (by norm_num [tp12414]) (by norm_num [tm12414])
    (by norm_num [ep12414]) (by norm_num [em12414])
    positive12414 negative12414 tails12414.1 tails12414.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12414.1 tailGuards12414.2

theorem preserves12414 : master12414.toScalarCertificate = scalar12414 := rfl

noncomputable def tp12415 : ℝ := (457722807 / 2000000000)
noncomputable def tm12415 : ℝ := (-((6000902713 / 10000000000)))
noncomputable def ep12415 : ℝ := (126470553276293 / 250000000000000000)
noncomputable def em12415 : ℝ := (49379482778627861 / 100000000000000000000)
noncomputable def bp12415 : ℝ := (4560896173674202289 / 10000000000000000000)
noncomputable def bm12415 : ℝ := (4647257425466088991 / 10000000000000000000)

theorem positive12415 :
    Eplus aL (agent12415.root+dsL) scalar12415.worldRadius world12415.frame
      agent12415.frame tp12415 ≤ -ep12415 := by
  apply positive_check (eT := (115500641939632424311 / 100000000000000000000)) (y := (37641730649146695869 / 100000000000000000000)) (u := (14570550454484097153 / 10000000000000000000))
  · norm_num [world12415, agent12415, scalar12415, tp12415, tm12415, ep12415, em12415, dsL]
  · norm_num [world12415, agent12415, scalar12415, tp12415, tm12415, ep12415, em12415, dsL]
  · norm_num [world12415, agent12415, scalar12415, tp12415, tm12415, ep12415, em12415, dsL]
  · norm_num [world12415, agent12415, scalar12415, tp12415, tm12415, ep12415, em12415, dsL]
  · norm_num [world12415, agent12415, scalar12415, tp12415, tm12415, ep12415, em12415, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12415, agent12415, tp12415, tm12415, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12415, agent12415, scalar12415, tp12415, tm12415, ep12415, em12415, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12415, agent12415, tp12415, tm12415, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12415, agent12415, scalar12415, tp12415, tm12415, ep12415, em12415, dsL]

theorem negative12415 :
    Eminus aL (agent12415.root+dsL) scalar12415.worldRadius world12415.frame
      agent12415.frame tm12415 ≤ -em12415 := by
  apply negative_check (lo := (34266474728547967033 / 50000000000000000000)) (hi := (68532949457095934067 / 100000000000000000000))
    (y := (-((71706223737722593797 / 100000000000000000000)))) (u := (24409216052388952013 / 50000000000000000000))
  · norm_num [world12415, agent12415, scalar12415, tp12415, tm12415, ep12415, em12415, dsL]
  · norm_num [world12415, agent12415, scalar12415, tp12415, tm12415, ep12415, em12415, dsL]
  · norm_num [world12415, agent12415, scalar12415, tp12415, tm12415, ep12415, em12415, dsL]
  · norm_num [world12415, agent12415, scalar12415, tp12415, tm12415, ep12415, em12415, dsL]
  · norm_num [world12415, agent12415, scalar12415, tp12415, tm12415, ep12415, em12415, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12415, agent12415, tp12415, tm12415, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12415, agent12415, tp12415, tm12415, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12415, agent12415, scalar12415, tp12415, tm12415, ep12415, em12415, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12415, agent12415, tp12415, tm12415, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12415, agent12415, scalar12415, tp12415, tm12415, ep12415, em12415, dsL]

theorem tails12415 :
    exp (-((12415:ℝ)*ep12415)) ≤ scalar12415.upperTail ∧
    exp (-((12415:ℝ)*em12415)) ≤ scalar12415.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12415:ℝ)) (by norm_num [ep12415]) ?_)
      (show bp12415^8 ≤ scalar12415.upperTail by norm_num [bp12415, scalar12415])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12415, bp12415, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12415:ℝ)) (by norm_num [em12415]) ?_)
      (show bm12415^8 ≤ scalar12415.lowerTail by norm_num [bm12415, scalar12415])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12415, bm12415, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12415 :
    agent12415.root+dsL+scalar12415.worldRadius < √(1/100/aL) ∧
    2*(agent12415.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12415, agent12415, scalar12415, tp12415, tm12415, ep12415, em12415, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12415, agent12415, scalar12415, tp12415, tm12415, ep12415, em12415, dsL]

noncomputable def master12415 : MasterCertificate 12415 world12415 agent12415 :=
  master scalar12415 dsL tp12415 tm12415 ep12415 em12415
    (by norm_num [dsL]) (by norm_num [tp12415]) (by norm_num [tm12415])
    (by norm_num [ep12415]) (by norm_num [em12415])
    positive12415 negative12415 tails12415.1 tails12415.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12415.1 tailGuards12415.2

theorem preserves12415 : master12415.toScalarCertificate = scalar12415 := rfl

noncomputable def tp12416 : ℝ := (228870943 / 1000000000)
noncomputable def tm12416 : ℝ := (-((240044391 / 400000000)))
noncomputable def ep12416 : ℝ := (50591188079736951 / 100000000000000000000)
noncomputable def em12416 : ℝ := (3086378091659143 / 6250000000000000000)
noncomputable def bp12416 : ℝ := (22801988941468212227 / 50000000000000000000)
noncomputable def bm12416 : ℝ := (46467854769886240239 / 100000000000000000000)

theorem positive12416 :
    Eplus aL (agent12416.root+dsL) scalar12416.worldRadius world12416.frame
      agent12416.frame tp12416 ≤ -ep12416 := by
  apply positive_check (eT := (28875238109566127143 / 25000000000000000000)) (y := (60228201789156221 / 160000000000000000)) (u := (1457068092984179399 / 1000000000000000000))
  · norm_num [world12416, agent12416, scalar12416, tp12416, tm12416, ep12416, em12416, dsL]
  · norm_num [world12416, agent12416, scalar12416, tp12416, tm12416, ep12416, em12416, dsL]
  · norm_num [world12416, agent12416, scalar12416, tp12416, tm12416, ep12416, em12416, dsL]
  · norm_num [world12416, agent12416, scalar12416, tp12416, tm12416, ep12416, em12416, dsL]
  · norm_num [world12416, agent12416, scalar12416, tp12416, tm12416, ep12416, em12416, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12416, agent12416, tp12416, tm12416, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12416, agent12416, scalar12416, tp12416, tm12416, ep12416, em12416, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12416, agent12416, tp12416, tm12416, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12416, agent12416, scalar12416, tp12416, tm12416, ep12416, em12416, dsL]

theorem negative12416 :
    Eminus aL (agent12416.root+dsL) scalar12416.worldRadius world12416.frame
      agent12416.frame tm12416 ≤ -em12416 := by
  apply negative_check (lo := (68532652234377554001 / 100000000000000000000)) (hi := (34266326117188777001 / 50000000000000000000))
    (y := (-((14341282052220783709 / 20000000000000000000)))) (u := (976366820941451089 / 2000000000000000000))
  · norm_num [world12416, agent12416, scalar12416, tp12416, tm12416, ep12416, em12416, dsL]
  · norm_num [world12416, agent12416, scalar12416, tp12416, tm12416, ep12416, em12416, dsL]
  · norm_num [world12416, agent12416, scalar12416, tp12416, tm12416, ep12416, em12416, dsL]
  · norm_num [world12416, agent12416, scalar12416, tp12416, tm12416, ep12416, em12416, dsL]
  · norm_num [world12416, agent12416, scalar12416, tp12416, tm12416, ep12416, em12416, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12416, agent12416, tp12416, tm12416, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12416, agent12416, tp12416, tm12416, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12416, agent12416, scalar12416, tp12416, tm12416, ep12416, em12416, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12416, agent12416, tp12416, tm12416, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12416, agent12416, scalar12416, tp12416, tm12416, ep12416, em12416, dsL]

theorem tails12416 :
    exp (-((12416:ℝ)*ep12416)) ≤ scalar12416.upperTail ∧
    exp (-((12416:ℝ)*em12416)) ≤ scalar12416.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12416:ℝ)) (by norm_num [ep12416]) ?_)
      (show bp12416^8 ≤ scalar12416.upperTail by norm_num [bp12416, scalar12416])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12416, bp12416, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12416:ℝ)) (by norm_num [em12416]) ?_)
      (show bm12416^8 ≤ scalar12416.lowerTail by norm_num [bm12416, scalar12416])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12416, bm12416, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12416 :
    agent12416.root+dsL+scalar12416.worldRadius < √(1/100/aL) ∧
    2*(agent12416.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12416, agent12416, scalar12416, tp12416, tm12416, ep12416, em12416, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12416, agent12416, scalar12416, tp12416, tm12416, ep12416, em12416, dsL]

noncomputable def master12416 : MasterCertificate 12416 world12416 agent12416 :=
  master scalar12416 dsL tp12416 tm12416 ep12416 em12416
    (by norm_num [dsL]) (by norm_num [tp12416]) (by norm_num [tm12416])
    (by norm_num [ep12416]) (by norm_num [em12416])
    positive12416 negative12416 tails12416.1 tails12416.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12416.1 tailGuards12416.2

theorem preserves12416 : master12416.toScalarCertificate = scalar12416 := rfl

noncomputable def tp12417 : ℝ := (1144402447 / 5000000000)
noncomputable def tm12417 : ℝ := (-((3000658267 / 5000000000)))
noncomputable def ep12417 : ℝ := (6324269240056707 / 12500000000000000000)
noncomputable def em12417 : ℝ := (24692307646404137 / 50000000000000000000)
noncomputable def bp12417 : ℝ := (45598994892681244367 / 100000000000000000000)
noncomputable def bm12417 : ℝ := (9292627217530283731 / 20000000000000000000)

theorem positive12417 :
    Eplus aL (agent12417.root+dsL) scalar12417.worldRadius world12417.frame
      agent12417.frame tp12417 ≤ -ep12417 := by
  apply positive_check (eT := (57750631735391256399 / 50000000000000000000)) (y := (37643523033969096343 / 100000000000000000000)) (u := (18213514521449370769 / 12500000000000000000))
  · norm_num [world12417, agent12417, scalar12417, tp12417, tm12417, ep12417, em12417, dsL]
  · norm_num [world12417, agent12417, scalar12417, tp12417, tm12417, ep12417, em12417, dsL]
  · norm_num [world12417, agent12417, scalar12417, tp12417, tm12417, ep12417, em12417, dsL]
  · norm_num [world12417, agent12417, scalar12417, tp12417, tm12417, ep12417, em12417, dsL]
  · norm_num [world12417, agent12417, scalar12417, tp12417, tm12417, ep12417, em12417, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12417, agent12417, tp12417, tm12417, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12417, agent12417, scalar12417, tp12417, tm12417, ep12417, em12417, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12417, agent12417, tp12417, tm12417, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12417, agent12417, scalar12417, tp12417, tm12417, ep12417, em12417, dsL]

theorem negative12417 :
    Eminus aL (agent12417.root+dsL) scalar12417.worldRadius world12417.frame
      agent12417.frame tm12417 ≤ -em12417 := by
  apply negative_check (lo := (8566544532902108707 / 12500000000000000000)) (hi := (68532356263216869657 / 100000000000000000000))
    (y := (-((71706594200522958293 / 100000000000000000000)))) (u := (48818251250982232851 / 100000000000000000000))
  · norm_num [world12417, agent12417, scalar12417, tp12417, tm12417, ep12417, em12417, dsL]
  · norm_num [world12417, agent12417, scalar12417, tp12417, tm12417, ep12417, em12417, dsL]
  · norm_num [world12417, agent12417, scalar12417, tp12417, tm12417, ep12417, em12417, dsL]
  · norm_num [world12417, agent12417, scalar12417, tp12417, tm12417, ep12417, em12417, dsL]
  · norm_num [world12417, agent12417, scalar12417, tp12417, tm12417, ep12417, em12417, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12417, agent12417, tp12417, tm12417, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12417, agent12417, tp12417, tm12417, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12417, agent12417, scalar12417, tp12417, tm12417, ep12417, em12417, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12417, agent12417, tp12417, tm12417, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12417, agent12417, scalar12417, tp12417, tm12417, ep12417, em12417, dsL]

theorem tails12417 :
    exp (-((12417:ℝ)*ep12417)) ≤ scalar12417.upperTail ∧
    exp (-((12417:ℝ)*em12417)) ≤ scalar12417.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12417:ℝ)) (by norm_num [ep12417]) ?_)
      (show bp12417^8 ≤ scalar12417.upperTail by norm_num [bp12417, scalar12417])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12417, bp12417, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12417:ℝ)) (by norm_num [em12417]) ?_)
      (show bm12417^8 ≤ scalar12417.lowerTail by norm_num [bm12417, scalar12417])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12417, bm12417, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12417 :
    agent12417.root+dsL+scalar12417.worldRadius < √(1/100/aL) ∧
    2*(agent12417.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12417, agent12417, scalar12417, tp12417, tm12417, ep12417, em12417, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12417, agent12417, scalar12417, tp12417, tm12417, ep12417, em12417, dsL]

noncomputable def master12417 : MasterCertificate 12417 world12417 agent12417 :=
  master scalar12417 dsL tp12417 tm12417 ep12417 em12417
    (by norm_num [dsL]) (by norm_num [tp12417]) (by norm_num [tm12417])
    (by norm_num [ep12417]) (by norm_num [em12417])
    positive12417 negative12417 tails12417.1 tails12417.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12417.1 tailGuards12417.2

theorem preserves12417 : master12417.toScalarCertificate = scalar12417 := rfl

noncomputable def tp12418 : ℝ := (572225051 / 2500000000)
noncomputable def tm12418 : ℝ := (-((6001523303 / 10000000000)))
noncomputable def ep12418 : ℝ := (6324639719205883 / 12500000000000000000)
noncomputable def em12418 : ℝ := (49387179255344269 / 100000000000000000000)
noncomputable def bp12418 : ℝ := (45594013529629488169 / 100000000000000000000)
noncomputable def bm12418 : ℝ := (46458418930602651409 / 100000000000000000000)

theorem positive12418 :
    Eplus aL (agent12418.root+dsL) scalar12418.worldRadius world12418.frame
      agent12418.frame tp12418 ≤ -ep12418 := by
  apply positive_check (eT := (115501573415432092523 / 100000000000000000000)) (y := (37644417910083386091 / 100000000000000000000)) (u := (72854710042278680719 / 50000000000000000000))
  · norm_num [world12418, agent12418, scalar12418, tp12418, tm12418, ep12418, em12418, dsL]
  · norm_num [world12418, agent12418, scalar12418, tp12418, tm12418, ep12418, em12418, dsL]
  · norm_num [world12418, agent12418, scalar12418, tp12418, tm12418, ep12418, em12418, dsL]
  · norm_num [world12418, agent12418, scalar12418, tp12418, tm12418, ep12418, em12418, dsL]
  · norm_num [world12418, agent12418, scalar12418, tp12418, tm12418, ep12418, em12418, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12418, agent12418, tp12418, tm12418, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12418, agent12418, scalar12418, tp12418, tm12418, ep12418, em12418, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12418, agent12418, tp12418, tm12418, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12418, agent12418, scalar12418, tp12418, tm12418, ep12418, em12418, dsL]

theorem negative12418 :
    Eminus aL (agent12418.root+dsL) scalar12418.worldRadius world12418.frame
      agent12418.frame tm12418 ≤ -em12418 := by
  apply negative_check (lo := (68532060192967574017 / 100000000000000000000)) (hi := (34266030096483787009 / 50000000000000000000))
    (y := (-((71706779491818836843 / 100000000000000000000)))) (u := (48818160795095668127 / 100000000000000000000))
  · norm_num [world12418, agent12418, scalar12418, tp12418, tm12418, ep12418, em12418, dsL]
  · norm_num [world12418, agent12418, scalar12418, tp12418, tm12418, ep12418, em12418, dsL]
  · norm_num [world12418, agent12418, scalar12418, tp12418, tm12418, ep12418, em12418, dsL]
  · norm_num [world12418, agent12418, scalar12418, tp12418, tm12418, ep12418, em12418, dsL]
  · norm_num [world12418, agent12418, scalar12418, tp12418, tm12418, ep12418, em12418, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12418, agent12418, tp12418, tm12418, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12418, agent12418, tp12418, tm12418, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12418, agent12418, scalar12418, tp12418, tm12418, ep12418, em12418, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12418, agent12418, tp12418, tm12418, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12418, agent12418, scalar12418, tp12418, tm12418, ep12418, em12418, dsL]

theorem tails12418 :
    exp (-((12418:ℝ)*ep12418)) ≤ scalar12418.upperTail ∧
    exp (-((12418:ℝ)*em12418)) ≤ scalar12418.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12418:ℝ)) (by norm_num [ep12418]) ?_)
      (show bp12418^8 ≤ scalar12418.upperTail by norm_num [bp12418, scalar12418])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12418, bp12418, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12418:ℝ)) (by norm_num [em12418]) ?_)
      (show bm12418^8 ≤ scalar12418.lowerTail by norm_num [bm12418, scalar12418])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12418, bm12418, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12418 :
    agent12418.root+dsL+scalar12418.worldRadius < √(1/100/aL) ∧
    2*(agent12418.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12418, agent12418, scalar12418, tp12418, tm12418, ep12418, em12418, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12418, agent12418, scalar12418, tp12418, tm12418, ep12418, em12418, dsL]

noncomputable def master12418 : MasterCertificate 12418 world12418 agent12418 :=
  master scalar12418 dsL tp12418 tm12418 ep12418 em12418
    (by norm_num [dsL]) (by norm_num [tp12418]) (by norm_num [tm12418])
    (by norm_num [ep12418]) (by norm_num [em12418])
    positive12418 negative12418 tails12418.1 tails12418.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12418.1 tailGuards12418.2

theorem preserves12418 : master12418.toScalarCertificate = scalar12418 := rfl

noncomputable def tp12419 : ℝ := (2288995587 / 10000000000)
noncomputable def tm12419 : ℝ := (-((6001729973 / 10000000000)))
noncomputable def ep12419 : ℝ := (10120016132383103 / 20000000000000000000)
noncomputable def em12419 : ℝ := (493897423654519 / 1000000000000000000)
noncomputable def bp12419 : ℝ := (9117806605508273881 / 20000000000000000000)
noncomputable def bm12419 : ℝ := (46453702569414561369 / 100000000000000000000)

theorem positive12419 :
    Eplus aL (agent12419.root+dsL) scalar12419.worldRadius world12419.frame
      agent12419.frame tp12419 ≤ -ep12419 := by
  apply positive_check (eT := (23100376784610098703 / 20000000000000000000)) (y := (18822657202388322653 / 50000000000000000000)) (u := (145710726367631368741 / 100000000000000000000))
  · norm_num [world12419, agent12419, scalar12419, tp12419, tm12419, ep12419, em12419, dsL]
  · norm_num [world12419, agent12419, scalar12419, tp12419, tm12419, ep12419, em12419, dsL]
  · norm_num [world12419, agent12419, scalar12419, tp12419, tm12419, ep12419, em12419, dsL]
  · norm_num [world12419, agent12419, scalar12419, tp12419, tm12419, ep12419, em12419, dsL]
  · norm_num [world12419, agent12419, scalar12419, tp12419, tm12419, ep12419, em12419, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12419, agent12419, tp12419, tm12419, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12419, agent12419, scalar12419, tp12419, tm12419, ep12419, em12419, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12419, agent12419, tp12419, tm12419, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12419, agent12419, scalar12419, tp12419, tm12419, ep12419, em12419, dsL]

theorem negative12419 :
    Eminus aL (agent12419.root+dsL) scalar12419.worldRadius world12419.frame
      agent12419.frame tm12419 ≤ -em12419 := by
  apply negative_check (lo := (8566470561742185031 / 12500000000000000000)) (hi := (68531764493937480249 / 100000000000000000000))
    (y := (-((71706964617702770187 / 100000000000000000000)))) (u := (1220451760503190749 / 2500000000000000000))
  · norm_num [world12419, agent12419, scalar12419, tp12419, tm12419, ep12419, em12419, dsL]
  · norm_num [world12419, agent12419, scalar12419, tp12419, tm12419, ep12419, em12419, dsL]
  · norm_num [world12419, agent12419, scalar12419, tp12419, tm12419, ep12419, em12419, dsL]
  · norm_num [world12419, agent12419, scalar12419, tp12419, tm12419, ep12419, em12419, dsL]
  · norm_num [world12419, agent12419, scalar12419, tp12419, tm12419, ep12419, em12419, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12419, agent12419, tp12419, tm12419, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12419, agent12419, tp12419, tm12419, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12419, agent12419, scalar12419, tp12419, tm12419, ep12419, em12419, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12419, agent12419, tp12419, tm12419, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12419, agent12419, scalar12419, tp12419, tm12419, ep12419, em12419, dsL]

theorem tails12419 :
    exp (-((12419:ℝ)*ep12419)) ≤ scalar12419.upperTail ∧
    exp (-((12419:ℝ)*em12419)) ≤ scalar12419.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12419:ℝ)) (by norm_num [ep12419]) ?_)
      (show bp12419^8 ≤ scalar12419.upperTail by norm_num [bp12419, scalar12419])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12419, bp12419, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12419:ℝ)) (by norm_num [em12419]) ?_)
      (show bm12419^8 ≤ scalar12419.lowerTail by norm_num [bm12419, scalar12419])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12419, bm12419, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12419 :
    agent12419.root+dsL+scalar12419.worldRadius < √(1/100/aL) ∧
    2*(agent12419.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12419, agent12419, scalar12419, tp12419, tm12419, ep12419, em12419, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12419, agent12419, scalar12419, tp12419, tm12419, ep12419, em12419, dsL]

noncomputable def master12419 : MasterCertificate 12419 world12419 agent12419 :=
  master scalar12419 dsL tp12419 tm12419 ep12419 em12419
    (by norm_num [dsL]) (by norm_num [tp12419]) (by norm_num [tm12419])
    (by norm_num [ep12419]) (by norm_num [em12419])
    positive12419 negative12419 tails12419.1 tails12419.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12419.1 tailGuards12419.2

theorem preserves12419 : master12419.toScalarCertificate = scalar12419 := rfl

noncomputable def tp12420 : ℝ := (2289167729 / 10000000000)
noncomputable def tm12420 : ℝ := (-((1500542151 / 2500000000)))
noncomputable def ep12420 : ℝ := (50604523074423869 / 100000000000000000000)
noncomputable def em12420 : ℝ := (49393914602290283 / 100000000000000000000)
noncomputable def bp12420 : ℝ := (1139575142748503003 / 2500000000000000000)
noncomputable def bm12420 : ℝ := (46447826029586149357 / 100000000000000000000)

theorem positive12420 :
    Eplus aL (agent12420.root+dsL) scalar12420.worldRadius world12420.frame
      agent12420.frame tp12420 ≤ -ep12420 := by
  apply positive_check (eT := (115502752649862917853 / 100000000000000000000)) (y := (294105277397539641 / 781250000000000000)) (u := (29142192222174568387 / 20000000000000000000))
  · norm_num [world12420, agent12420, scalar12420, tp12420, tm12420, ep12420, em12420, dsL]
  · norm_num [world12420, agent12420, scalar12420, tp12420, tm12420, ep12420, em12420, dsL]
  · norm_num [world12420, agent12420, scalar12420, tp12420, tm12420, ep12420, em12420, dsL]
  · norm_num [world12420, agent12420, scalar12420, tp12420, tm12420, ep12420, em12420, dsL]
  · norm_num [world12420, agent12420, scalar12420, tp12420, tm12420, ep12420, em12420, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12420, agent12420, tp12420, tm12420, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12420, agent12420, scalar12420, tp12420, tm12420, ep12420, em12420, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12420, agent12420, tp12420, tm12420, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12420, agent12420, scalar12420, tp12420, tm12420, ep12420, em12420, dsL]

theorem negative12420 :
    Eminus aL (agent12420.root+dsL) scalar12420.worldRadius world12420.frame
      agent12420.frame tm12420 ≤ -em12420 := by
  apply negative_check (lo := (68530467907244075723 / 100000000000000000000)) (hi := (17132616976811018931 / 25000000000000000000))
    (y := (-((71705208018064199783 / 100000000000000000000)))) (u := (48818927965707986199 / 100000000000000000000))
  · norm_num [world12420, agent12420, scalar12420, tp12420, tm12420, ep12420, em12420, dsL]
  · norm_num [world12420, agent12420, scalar12420, tp12420, tm12420, ep12420, em12420, dsL]
  · norm_num [world12420, agent12420, scalar12420, tp12420, tm12420, ep12420, em12420, dsL]
  · norm_num [world12420, agent12420, scalar12420, tp12420, tm12420, ep12420, em12420, dsL]
  · norm_num [world12420, agent12420, scalar12420, tp12420, tm12420, ep12420, em12420, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12420, agent12420, tp12420, tm12420, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12420, agent12420, tp12420, tm12420, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12420, agent12420, scalar12420, tp12420, tm12420, ep12420, em12420, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12420, agent12420, tp12420, tm12420, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12420, agent12420, scalar12420, tp12420, tm12420, ep12420, em12420, dsL]

theorem tails12420 :
    exp (-((12420:ℝ)*ep12420)) ≤ scalar12420.upperTail ∧
    exp (-((12420:ℝ)*em12420)) ≤ scalar12420.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12420:ℝ)) (by norm_num [ep12420]) ?_)
      (show bp12420^8 ≤ scalar12420.upperTail by norm_num [bp12420, scalar12420])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12420, bp12420, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12420:ℝ)) (by norm_num [em12420]) ?_)
      (show bm12420^8 ≤ scalar12420.lowerTail by norm_num [bm12420, scalar12420])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12420, bm12420, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12420 :
    agent12420.root+dsL+scalar12420.worldRadius < √(1/100/aL) ∧
    2*(agent12420.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12420, agent12420, scalar12420, tp12420, tm12420, ep12420, em12420, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12420, agent12420, scalar12420, tp12420, tm12420, ep12420, em12420, dsL]

noncomputable def master12420 : MasterCertificate 12420 world12420 agent12420 :=
  master scalar12420 dsL tp12420 tm12420 ep12420 em12420
    (by norm_num [dsL]) (by norm_num [tp12420]) (by norm_num [tm12420])
    (by norm_num [ep12420]) (by norm_num [em12420])
    positive12420 negative12420 tails12420.1 tails12420.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12420.1 tailGuards12420.2

theorem preserves12420 : master12420.toScalarCertificate = scalar12420 := rfl

noncomputable def tp12421 : ℝ := (1144631461 / 5000000000)
noncomputable def tm12421 : ℝ := (-((6002374877 / 10000000000)))
noncomputable def ep12421 : ℝ := (25303741281317579 / 50000000000000000000)
noncomputable def em12421 : ℝ := (24698237264267297 / 50000000000000000000)
noncomputable def bp12421 : ℝ := (45578028071015615159 / 100000000000000000000)
noncomputable def bm12421 : ℝ := (23221556175500314473 / 50000000000000000000)

theorem positive12421 :
    Eplus aL (agent12421.root+dsL) scalar12421.worldRadius world12421.frame
      agent12421.frame tp12421 ≤ -ep12421 := by
  apply positive_check (eT := (23100612365727365481 / 20000000000000000000)) (y := (37646369656185307593 / 100000000000000000000)) (u := (29142452798047362611 / 20000000000000000000))
  · norm_num [world12421, agent12421, scalar12421, tp12421, tm12421, ep12421, em12421, dsL]
  · norm_num [world12421, agent12421, scalar12421, tp12421, tm12421, ep12421, em12421, dsL]
  · norm_num [world12421, agent12421, scalar12421, tp12421, tm12421, ep12421, em12421, dsL]
  · norm_num [world12421, agent12421, scalar12421, tp12421, tm12421, ep12421, em12421, dsL]
  · norm_num [world12421, agent12421, scalar12421, tp12421, tm12421, ep12421, em12421, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12421, agent12421, tp12421, tm12421, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12421, agent12421, scalar12421, tp12421, tm12421, ep12421, em12421, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12421, agent12421, tp12421, tm12421, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12421, agent12421, scalar12421, tp12421, tm12421, ep12421, em12421, dsL]

theorem negative12421 :
    Eminus aL (agent12421.root+dsL) scalar12421.worldRadius world12421.frame
      agent12421.frame tm12421 ≤ -em12421 := by
  apply negative_check (lo := (68530173836536313803 / 100000000000000000000)) (hi := (17132543459134078451 / 25000000000000000000))
    (y := (-((2868215636466740519 / 4000000000000000000)))) (u := (9763767735818538487 / 20000000000000000000))
  · norm_num [world12421, agent12421, scalar12421, tp12421, tm12421, ep12421, em12421, dsL]
  · norm_num [world12421, agent12421, scalar12421, tp12421, tm12421, ep12421, em12421, dsL]
  · norm_num [world12421, agent12421, scalar12421, tp12421, tm12421, ep12421, em12421, dsL]
  · norm_num [world12421, agent12421, scalar12421, tp12421, tm12421, ep12421, em12421, dsL]
  · norm_num [world12421, agent12421, scalar12421, tp12421, tm12421, ep12421, em12421, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12421, agent12421, tp12421, tm12421, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12421, agent12421, tp12421, tm12421, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12421, agent12421, scalar12421, tp12421, tm12421, ep12421, em12421, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12421, agent12421, tp12421, tm12421, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12421, agent12421, scalar12421, tp12421, tm12421, ep12421, em12421, dsL]

theorem tails12421 :
    exp (-((12421:ℝ)*ep12421)) ≤ scalar12421.upperTail ∧
    exp (-((12421:ℝ)*em12421)) ≤ scalar12421.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12421:ℝ)) (by norm_num [ep12421]) ?_)
      (show bp12421^8 ≤ scalar12421.upperTail by norm_num [bp12421, scalar12421])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12421, bp12421, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12421:ℝ)) (by norm_num [em12421]) ?_)
      (show bm12421^8 ≤ scalar12421.lowerTail by norm_num [bm12421, scalar12421])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12421, bm12421, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12421 :
    agent12421.root+dsL+scalar12421.worldRadius < √(1/100/aL) ∧
    2*(agent12421.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12421, agent12421, scalar12421, tp12421, tm12421, ep12421, em12421, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12421, agent12421, scalar12421, tp12421, tm12421, ep12421, em12421, dsL]

noncomputable def master12421 : MasterCertificate 12421 world12421 agent12421 :=
  master scalar12421 dsL tp12421 tm12421 ep12421 em12421
    (by norm_num [dsL]) (by norm_num [tp12421]) (by norm_num [tm12421])
    (by norm_num [ep12421]) (by norm_num [em12421])
    positive12421 negative12421 tails12421.1 tails12421.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12421.1 tailGuards12421.2

theorem preserves12421 : master12421.toScalarCertificate = scalar12421 := rfl

noncomputable def tp12422 : ℝ := (2289358073 / 10000000000)
noncomputable def tm12422 : ℝ := (-((6002581223 / 10000000000)))
noncomputable def ep12422 : ℝ := (50610440515294471 / 100000000000000000000)
noncomputable def em12422 : ℝ := (4939903302121191 / 10000000000000000000)
noncomputable def bp12422 : ℝ := (45573051725075422081 / 100000000000000000000)
noncomputable def bm12422 : ℝ := (23219199943641470481 / 50000000000000000000)

theorem positive12422 :
    Eplus aL (agent12422.root+dsL) scalar12422.worldRadius world12422.frame
      agent12422.frame tp12422 ≤ -ep12422 := by
  apply positive_check (eT := (57751685367058278421 / 50000000000000000000)) (y := (18823631796253611501 / 50000000000000000000)) (u := (1138387238835251713 / 781250000000000000))
  · norm_num [world12422, agent12422, scalar12422, tp12422, tm12422, ep12422, em12422, dsL]
  · norm_num [world12422, agent12422, scalar12422, tp12422, tm12422, ep12422, em12422, dsL]
  · norm_num [world12422, agent12422, scalar12422, tp12422, tm12422, ep12422, em12422, dsL]
  · norm_num [world12422, agent12422, scalar12422, tp12422, tm12422, ep12422, em12422, dsL]
  · norm_num [world12422, agent12422, scalar12422, tp12422, tm12422, ep12422, em12422, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12422, agent12422, tp12422, tm12422, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12422, agent12422, scalar12422, tp12422, tm12422, ep12422, em12422, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12422, agent12422, tp12422, tm12422, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12422, agent12422, scalar12422, tp12422, tm12422, ep12422, em12422, dsL]

theorem negative12422 :
    Eminus aL (agent12422.root+dsL) scalar12422.worldRadius world12422.frame
      agent12422.frame tm12422 ≤ -em12422 := by
  apply negative_check (lo := (34264939697432847349 / 50000000000000000000)) (hi := (68529879394865694699 / 100000000000000000000))
    (y := (-((14341115097875767519 / 20000000000000000000)))) (u := (48818748570481211727 / 100000000000000000000))
  · norm_num [world12422, agent12422, scalar12422, tp12422, tm12422, ep12422, em12422, dsL]
  · norm_num [world12422, agent12422, scalar12422, tp12422, tm12422, ep12422, em12422, dsL]
  · norm_num [world12422, agent12422, scalar12422, tp12422, tm12422, ep12422, em12422, dsL]
  · norm_num [world12422, agent12422, scalar12422, tp12422, tm12422, ep12422, em12422, dsL]
  · norm_num [world12422, agent12422, scalar12422, tp12422, tm12422, ep12422, em12422, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12422, agent12422, tp12422, tm12422, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12422, agent12422, tp12422, tm12422, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12422, agent12422, scalar12422, tp12422, tm12422, ep12422, em12422, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12422, agent12422, tp12422, tm12422, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12422, agent12422, scalar12422, tp12422, tm12422, ep12422, em12422, dsL]

theorem tails12422 :
    exp (-((12422:ℝ)*ep12422)) ≤ scalar12422.upperTail ∧
    exp (-((12422:ℝ)*em12422)) ≤ scalar12422.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12422:ℝ)) (by norm_num [ep12422]) ?_)
      (show bp12422^8 ≤ scalar12422.upperTail by norm_num [bp12422, scalar12422])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12422, bp12422, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12422:ℝ)) (by norm_num [em12422]) ?_)
      (show bm12422^8 ≤ scalar12422.lowerTail by norm_num [bm12422, scalar12422])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12422, bm12422, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12422 :
    agent12422.root+dsL+scalar12422.worldRadius < √(1/100/aL) ∧
    2*(agent12422.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12422, agent12422, scalar12422, tp12422, tm12422, ep12422, em12422, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12422, agent12422, scalar12422, tp12422, tm12422, ep12422, em12422, dsL]

noncomputable def master12422 : MasterCertificate 12422 world12422 agent12422 :=
  master scalar12422 dsL tp12422 tm12422 ep12422 em12422
    (by norm_num [dsL]) (by norm_num [tp12422]) (by norm_num [tm12422])
    (by norm_num [ep12422]) (by norm_num [em12422])
    positive12422 negative12422 tails12422.1 tails12422.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12422.1 tailGuards12422.2

theorem preserves12422 : master12422.toScalarCertificate = scalar12422 := rfl

noncomputable def tp12423 : ℝ := (2289453259 / 10000000000)
noncomputable def tm12423 : ℝ := (-((187587107 / 312500000)))
noncomputable def ep12423 : ℝ := (12653349349933717 / 25000000000000000000)
noncomputable def em12423 : ℝ := (49401590506333957 / 100000000000000000000)
noncomputable def bp12423 : ℝ := (22784038170692548643 / 50000000000000000000)
noncomputable def bm12423 : ℝ := (23216844165615585037 / 50000000000000000000)

theorem positive12423 :
    Eplus aL (agent12423.root+dsL) scalar12423.worldRadius world12423.frame
      agent12423.frame tp12423 ≤ -ep12423 := by
  apply positive_check (eT := (1443795999077616043 / 1250000000000000000)) (y := (37648158524854775981 / 100000000000000000000)) (u := (29142974122917876229 / 20000000000000000000))
  · norm_num [world12423, agent12423, scalar12423, tp12423, tm12423, ep12423, em12423, dsL]
  · norm_num [world12423, agent12423, scalar12423, tp12423, tm12423, ep12423, em12423, dsL]
  · norm_num [world12423, agent12423, scalar12423, tp12423, tm12423, ep12423, em12423, dsL]
  · norm_num [world12423, agent12423, scalar12423, tp12423, tm12423, ep12423, em12423, dsL]
  · norm_num [world12423, agent12423, scalar12423, tp12423, tm12423, ep12423, em12423, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12423, agent12423, tp12423, tm12423, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12423, agent12423, scalar12423, tp12423, tm12423, ep12423, em12423, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12423, agent12423, tp12423, tm12423, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12423, agent12423, scalar12423, tp12423, tm12423, ep12423, em12423, dsL]

theorem negative12423 :
    Eminus aL (agent12423.root+dsL) scalar12423.worldRadius world12423.frame
      agent12423.frame tm12423 ≤ -em12423 := by
  apply negative_check (lo := (34264792761400338433 / 50000000000000000000)) (hi := (68529585522800676867 / 100000000000000000000))
    (y := (-((71705759322581275097 / 100000000000000000000)))) (u := (24409329412747407633 / 50000000000000000000))
  · norm_num [world12423, agent12423, scalar12423, tp12423, tm12423, ep12423, em12423, dsL]
  · norm_num [world12423, agent12423, scalar12423, tp12423, tm12423, ep12423, em12423, dsL]
  · norm_num [world12423, agent12423, scalar12423, tp12423, tm12423, ep12423, em12423, dsL]
  · norm_num [world12423, agent12423, scalar12423, tp12423, tm12423, ep12423, em12423, dsL]
  · norm_num [world12423, agent12423, scalar12423, tp12423, tm12423, ep12423, em12423, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12423, agent12423, tp12423, tm12423, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12423, agent12423, tp12423, tm12423, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12423, agent12423, scalar12423, tp12423, tm12423, ep12423, em12423, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12423, agent12423, tp12423, tm12423, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12423, agent12423, scalar12423, tp12423, tm12423, ep12423, em12423, dsL]

theorem tails12423 :
    exp (-((12423:ℝ)*ep12423)) ≤ scalar12423.upperTail ∧
    exp (-((12423:ℝ)*em12423)) ≤ scalar12423.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12423:ℝ)) (by norm_num [ep12423]) ?_)
      (show bp12423^8 ≤ scalar12423.upperTail by norm_num [bp12423, scalar12423])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12423, bp12423, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12423:ℝ)) (by norm_num [em12423]) ?_)
      (show bm12423^8 ≤ scalar12423.lowerTail by norm_num [bm12423, scalar12423])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12423, bm12423, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12423 :
    agent12423.root+dsL+scalar12423.worldRadius < √(1/100/aL) ∧
    2*(agent12423.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12423, agent12423, scalar12423, tp12423, tm12423, ep12423, em12423, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12423, agent12423, scalar12423, tp12423, tm12423, ep12423, em12423, dsL]

noncomputable def master12423 : MasterCertificate 12423 world12423 agent12423 :=
  master scalar12423 dsL tp12423 tm12423 ep12423 em12423
    (by norm_num [dsL]) (by norm_num [tp12423]) (by norm_num [tm12423])
    (by norm_num [ep12423]) (by norm_num [em12423])
    positive12423 negative12423 tails12423.1 tails12423.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12423.1 tailGuards12423.2

theorem preserves12423 : master12423.toScalarCertificate = scalar12423 := rfl

noncomputable def tp12424 : ℝ := (572387083 / 2500000000)
noncomputable def tm12424 : ℝ := (-((3001496689 / 5000000000)))
noncomputable def ep12424 : ℝ := (25308176213158099 / 50000000000000000000)
noncomputable def em12424 : ℝ := (24702073141414441 / 50000000000000000000)
noncomputable def bp12424 : ℝ := (5695387809834504487 / 12500000000000000000)
noncomputable def bm12424 : ℝ := (46428978188343762563 / 100000000000000000000)

theorem positive12424 :
    Eplus aL (agent12424.root+dsL) scalar12424.worldRadius world12424.frame
      agent12424.frame tp12424 ≤ -ep12424 := by
  apply positive_check (eT := (115503988328744862021 / 100000000000000000000)) (y := (37649051989128092059 / 100000000000000000000)) (u := (29143234506143060063 / 20000000000000000000))
  · norm_num [world12424, agent12424, scalar12424, tp12424, tm12424, ep12424, em12424, dsL]
  · norm_num [world12424, agent12424, scalar12424, tp12424, tm12424, ep12424, em12424, dsL]
  · norm_num [world12424, agent12424, scalar12424, tp12424, tm12424, ep12424, em12424, dsL]
  · norm_num [world12424, agent12424, scalar12424, tp12424, tm12424, ep12424, em12424, dsL]
  · norm_num [world12424, agent12424, scalar12424, tp12424, tm12424, ep12424, em12424, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12424, agent12424, tp12424, tm12424, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12424, agent12424, scalar12424, tp12424, tm12424, ep12424, em12424, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12424, agent12424, tp12424, tm12424, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12424, agent12424, scalar12424, tp12424, tm12424, ep12424, em12424, dsL]

theorem negative12424 :
    Eminus aL (agent12424.root+dsL) scalar12424.worldRadius world12424.frame
      agent12424.frame tm12424 ≤ -em12424 := by
  apply negative_check (lo := (3426464633016211019 / 5000000000000000000)) (hi := (68529292660324220381 / 100000000000000000000))
    (y := (-((71705941690052242459 / 100000000000000000000)))) (u := (48818569796222535267 / 100000000000000000000))
  · norm_num [world12424, agent12424, scalar12424, tp12424, tm12424, ep12424, em12424, dsL]
  · norm_num [world12424, agent12424, scalar12424, tp12424, tm12424, ep12424, em12424, dsL]
  · norm_num [world12424, agent12424, scalar12424, tp12424, tm12424, ep12424, em12424, dsL]
  · norm_num [world12424, agent12424, scalar12424, tp12424, tm12424, ep12424, em12424, dsL]
  · norm_num [world12424, agent12424, scalar12424, tp12424, tm12424, ep12424, em12424, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12424, agent12424, tp12424, tm12424, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12424, agent12424, tp12424, tm12424, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12424, agent12424, scalar12424, tp12424, tm12424, ep12424, em12424, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12424, agent12424, tp12424, tm12424, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12424, agent12424, scalar12424, tp12424, tm12424, ep12424, em12424, dsL]

theorem tails12424 :
    exp (-((12424:ℝ)*ep12424)) ≤ scalar12424.upperTail ∧
    exp (-((12424:ℝ)*em12424)) ≤ scalar12424.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12424:ℝ)) (by norm_num [ep12424]) ?_)
      (show bp12424^8 ≤ scalar12424.upperTail by norm_num [bp12424, scalar12424])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12424, bp12424, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12424:ℝ)) (by norm_num [em12424]) ?_)
      (show bm12424^8 ≤ scalar12424.lowerTail by norm_num [bm12424, scalar12424])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12424, bm12424, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12424 :
    agent12424.root+dsL+scalar12424.worldRadius < √(1/100/aL) ∧
    2*(agent12424.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12424, agent12424, scalar12424, tp12424, tm12424, ep12424, em12424, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12424, agent12424, scalar12424, tp12424, tm12424, ep12424, em12424, dsL]

noncomputable def master12424 : MasterCertificate 12424 world12424 agent12424 :=
  master scalar12424 dsL tp12424 tm12424 ep12424 em12424
    (by norm_num [dsL]) (by norm_num [tp12424]) (by norm_num [tm12424])
    (by norm_num [ep12424]) (by norm_num [em12424])
    positive12424 negative12424 tails12424.1 tails12424.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12424.1 tailGuards12424.2

theorem preserves12424 : master12424.toScalarCertificate = scalar12424 := rfl

end BstLean.Part268
