import BstLean.Part261Checker
import BstLean.Part268Scalar29
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp13075 : ℝ := (2348858709 / 10000000000)
noncomputable def tm13075 : ℝ := (-((3067177171 / 5000000000)))
noncomputable def ep13075 : ℝ := (2095116596432213 / 4000000000000000000)
noncomputable def em13075 : ℝ := (50935064189052221 / 100000000000000000000)
noncomputable def bp13075 : ℝ := (10620905523495441297 / 25000000000000000000)
noncomputable def bm13075 : ℝ := (43497359306238634851 / 100000000000000000000)

theorem positive13075 :
    Eplus aL (agent13075.root+dsL) scalar13075.worldRadius world13075.frame
      agent13075.frame tp13075 ≤ -ep13075 := by
  apply positive_check (eT := (57846333924698222713 / 50000000000000000000)) (y := (38106942411307146323 / 100000000000000000000)) (u := (146384922831649382959 / 100000000000000000000))
  · norm_num [world13075, agent13075, scalar13075, tp13075, tm13075, ep13075, em13075, dsL]
  · norm_num [world13075, agent13075, scalar13075, tp13075, tm13075, ep13075, em13075, dsL]
  · norm_num [world13075, agent13075, scalar13075, tp13075, tm13075, ep13075, em13075, dsL]
  · norm_num [world13075, agent13075, scalar13075, tp13075, tm13075, ep13075, em13075, dsL]
  · norm_num [world13075, agent13075, scalar13075, tp13075, tm13075, ep13075, em13075, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13075, agent13075, tp13075, tm13075, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13075, agent13075, scalar13075, tp13075, tm13075, ep13075, em13075, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13075, agent13075, tp13075, tm13075, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13075, agent13075, scalar13075, tp13075, tm13075, ep13075, em13075, dsL]

theorem negative13075 :
    Eminus aL (agent13075.root+dsL) scalar13075.worldRadius world13075.frame
      agent13075.frame tm13075 ≤ -em13075 := by
  apply negative_check (lo := (68338974771995977967 / 100000000000000000000)) (hi := (4271185923249748623 / 6250000000000000000))
    (y := (-((17904149849083277993 / 25000000000000000000)))) (u := (4886220491564515557 / 10000000000000000000))
  · norm_num [world13075, agent13075, scalar13075, tp13075, tm13075, ep13075, em13075, dsL]
  · norm_num [world13075, agent13075, scalar13075, tp13075, tm13075, ep13075, em13075, dsL]
  · norm_num [world13075, agent13075, scalar13075, tp13075, tm13075, ep13075, em13075, dsL]
  · norm_num [world13075, agent13075, scalar13075, tp13075, tm13075, ep13075, em13075, dsL]
  · norm_num [world13075, agent13075, scalar13075, tp13075, tm13075, ep13075, em13075, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13075, agent13075, tp13075, tm13075, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13075, agent13075, tp13075, tm13075, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13075, agent13075, scalar13075, tp13075, tm13075, ep13075, em13075, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13075, agent13075, tp13075, tm13075, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13075, agent13075, scalar13075, tp13075, tm13075, ep13075, em13075, dsL]

theorem tails13075 :
    exp (-((13075:ℝ)*ep13075)) ≤ scalar13075.upperTail ∧
    exp (-((13075:ℝ)*em13075)) ≤ scalar13075.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13075:ℝ)) (by norm_num [ep13075]) ?_)
      (show bp13075^8 ≤ scalar13075.upperTail by norm_num [bp13075, scalar13075])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13075, bp13075, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13075:ℝ)) (by norm_num [em13075]) ?_)
      (show bm13075^8 ≤ scalar13075.lowerTail by norm_num [bm13075, scalar13075])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13075, bm13075, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13075 :
    agent13075.root+dsL+scalar13075.worldRadius < √(1/100/aL) ∧
    2*(agent13075.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13075, agent13075, scalar13075, tp13075, tm13075, ep13075, em13075, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13075, agent13075, scalar13075, tp13075, tm13075, ep13075, em13075, dsL]

noncomputable def master13075 : MasterCertificate 13075 world13075 agent13075 :=
  master scalar13075 dsL tp13075 tm13075 ep13075 em13075
    (by norm_num [dsL]) (by norm_num [tp13075]) (by norm_num [tm13075])
    (by norm_num [ep13075]) (by norm_num [em13075])
    positive13075 negative13075 tails13075.1 tails13075.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13075.1 tailGuards13075.2

theorem preserves13075 : master13075.toScalarCertificate = scalar13075 := rfl

noncomputable def tp13076 : ℝ := (23489321 / 100000000)
noncomputable def tm13076 : ℝ := (-((1533627547 / 2500000000)))
noncomputable def ep13076 : ℝ := (52380117338337307 / 100000000000000000000)
noncomputable def em13076 : ℝ := (50936931921800979 / 100000000000000000000)
noncomputable def bp13076 : ℝ := (21239655727013347387 / 50000000000000000000)
noncomputable def bm13076 : ℝ := (5436657772730937471 / 12500000000000000000)

theorem positive13076 :
    Eplus aL (agent13076.root+dsL) scalar13076.worldRadius world13076.frame
      agent13076.frame tp13076 ≤ -ep13076 := by
  apply positive_check (eT := (115692840202342274279 / 100000000000000000000)) (y := (19053800866562878259 / 50000000000000000000)) (u := (73192943991283244757 / 50000000000000000000))
  · norm_num [world13076, agent13076, scalar13076, tp13076, tm13076, ep13076, em13076, dsL]
  · norm_num [world13076, agent13076, scalar13076, tp13076, tm13076, ep13076, em13076, dsL]
  · norm_num [world13076, agent13076, scalar13076, tp13076, tm13076, ep13076, em13076, dsL]
  · norm_num [world13076, agent13076, scalar13076, tp13076, tm13076, ep13076, em13076, dsL]
  · norm_num [world13076, agent13076, scalar13076, tp13076, tm13076, ep13076, em13076, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13076, agent13076, tp13076, tm13076, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13076, agent13076, scalar13076, tp13076, tm13076, ep13076, em13076, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13076, agent13076, tp13076, tm13076, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13076, agent13076, scalar13076, tp13076, tm13076, ep13076, em13076, dsL]

theorem negative13076 :
    Eminus aL (agent13076.root+dsL) scalar13076.worldRadius world13076.frame
      agent13076.frame tm13076 ≤ -em13076 := by
  apply negative_check (lo := (34169430408069000007 / 50000000000000000000)) (hi := (13667772163227600003 / 20000000000000000000))
    (y := (-((17904130165173387509 / 25000000000000000000)))) (u := (48862243387629845547 / 100000000000000000000))
  · norm_num [world13076, agent13076, scalar13076, tp13076, tm13076, ep13076, em13076, dsL]
  · norm_num [world13076, agent13076, scalar13076, tp13076, tm13076, ep13076, em13076, dsL]
  · norm_num [world13076, agent13076, scalar13076, tp13076, tm13076, ep13076, em13076, dsL]
  · norm_num [world13076, agent13076, scalar13076, tp13076, tm13076, ep13076, em13076, dsL]
  · norm_num [world13076, agent13076, scalar13076, tp13076, tm13076, ep13076, em13076, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13076, agent13076, tp13076, tm13076, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13076, agent13076, tp13076, tm13076, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13076, agent13076, scalar13076, tp13076, tm13076, ep13076, em13076, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13076, agent13076, tp13076, tm13076, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13076, agent13076, scalar13076, tp13076, tm13076, ep13076, em13076, dsL]

theorem tails13076 :
    exp (-((13076:ℝ)*ep13076)) ≤ scalar13076.upperTail ∧
    exp (-((13076:ℝ)*em13076)) ≤ scalar13076.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13076:ℝ)) (by norm_num [ep13076]) ?_)
      (show bp13076^8 ≤ scalar13076.upperTail by norm_num [bp13076, scalar13076])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13076, bp13076, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13076:ℝ)) (by norm_num [em13076]) ?_)
      (show bm13076^8 ≤ scalar13076.lowerTail by norm_num [bm13076, scalar13076])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13076, bm13076, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13076 :
    agent13076.root+dsL+scalar13076.worldRadius < √(1/100/aL) ∧
    2*(agent13076.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13076, agent13076, scalar13076, tp13076, tm13076, ep13076, em13076, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13076, agent13076, scalar13076, tp13076, tm13076, ep13076, em13076, dsL]

noncomputable def master13076 : MasterCertificate 13076 world13076 agent13076 :=
  master scalar13076 dsL tp13076 tm13076 ep13076 em13076
    (by norm_num [dsL]) (by norm_num [tp13076]) (by norm_num [tm13076])
    (by norm_num [ep13076]) (by norm_num [em13076])
    positive13076 negative13076 tails13076.1 tails13076.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13076.1 tailGuards13076.2

theorem preserves13076 : master13076.toScalarCertificate = scalar13076 := rfl

noncomputable def tp13077 : ℝ := (1174502787 / 5000000000)
noncomputable def tm13077 : ℝ := (-((766833247 / 1250000000)))
noncomputable def ep13077 : ℝ := (5238231950301231 / 10000000000000000000)
noncomputable def em13077 : ℝ := (3183674979692463 / 6250000000000000000)
noncomputable def bp13077 : ℝ := (21237500600043923061 / 50000000000000000000)
noncomputable def bm13077 : ℝ := (21744582612857559397 / 50000000000000000000)

theorem positive13077 :
    Eplus aL (agent13077.root+dsL) scalar13077.worldRadius world13077.frame
      agent13077.frame tp13077 ≤ -ep13077 := by
  apply positive_check (eT := (28923253296051476441 / 25000000000000000000)) (y := (4763532591591653501 / 12500000000000000000)) (u := (146386852668172321969 / 100000000000000000000))
  · norm_num [world13077, agent13077, scalar13077, tp13077, tm13077, ep13077, em13077, dsL]
  · norm_num [world13077, agent13077, scalar13077, tp13077, tm13077, ep13077, em13077, dsL]
  · norm_num [world13077, agent13077, scalar13077, tp13077, tm13077, ep13077, em13077, dsL]
  · norm_num [world13077, agent13077, scalar13077, tp13077, tm13077, ep13077, em13077, dsL]
  · norm_num [world13077, agent13077, scalar13077, tp13077, tm13077, ep13077, em13077, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13077, agent13077, tp13077, tm13077, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13077, agent13077, scalar13077, tp13077, tm13077, ep13077, em13077, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13077, agent13077, tp13077, tm13077, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13077, agent13077, scalar13077, tp13077, tm13077, ep13077, em13077, dsL]

theorem negative13077 :
    Eminus aL (agent13077.root+dsL) scalar13077.worldRadius world13077.frame
      agent13077.frame tm13077 ≤ -em13077 := by
  apply negative_check (lo := (68338747049503260847 / 100000000000000000000)) (hi := (4271171690593953803 / 6250000000000000000))
    (y := (-((71616437564054683861 / 100000000000000000000)))) (u := (48862283990528645097 / 100000000000000000000))
  · norm_num [world13077, agent13077, scalar13077, tp13077, tm13077, ep13077, em13077, dsL]
  · norm_num [world13077, agent13077, scalar13077, tp13077, tm13077, ep13077, em13077, dsL]
  · norm_num [world13077, agent13077, scalar13077, tp13077, tm13077, ep13077, em13077, dsL]
  · norm_num [world13077, agent13077, scalar13077, tp13077, tm13077, ep13077, em13077, dsL]
  · norm_num [world13077, agent13077, scalar13077, tp13077, tm13077, ep13077, em13077, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13077, agent13077, tp13077, tm13077, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13077, agent13077, tp13077, tm13077, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13077, agent13077, scalar13077, tp13077, tm13077, ep13077, em13077, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13077, agent13077, tp13077, tm13077, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13077, agent13077, scalar13077, tp13077, tm13077, ep13077, em13077, dsL]

theorem tails13077 :
    exp (-((13077:ℝ)*ep13077)) ≤ scalar13077.upperTail ∧
    exp (-((13077:ℝ)*em13077)) ≤ scalar13077.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13077:ℝ)) (by norm_num [ep13077]) ?_)
      (show bp13077^8 ≤ scalar13077.upperTail by norm_num [bp13077, scalar13077])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13077, bp13077, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13077:ℝ)) (by norm_num [em13077]) ?_)
      (show bm13077^8 ≤ scalar13077.lowerTail by norm_num [bm13077, scalar13077])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13077, bm13077, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13077 :
    agent13077.root+dsL+scalar13077.worldRadius < √(1/100/aL) ∧
    2*(agent13077.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13077, agent13077, scalar13077, tp13077, tm13077, ep13077, em13077, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13077, agent13077, scalar13077, tp13077, tm13077, ep13077, em13077, dsL]

noncomputable def master13077 : MasterCertificate 13077 world13077 agent13077 :=
  master scalar13077 dsL tp13077 tm13077 ep13077 em13077
    (by norm_num [dsL]) (by norm_num [tp13077]) (by norm_num [tm13077])
    (by norm_num [ep13077]) (by norm_num [em13077])
    positive13077 negative13077 tails13077.1 tails13077.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13077.1 tailGuards13077.2

theorem preserves13077 : master13077.toScalarCertificate = scalar13077 := rfl

noncomputable def tp13078 : ℝ := (146817439 / 625000000)
noncomputable def tm13078 : ℝ := (-((3067410959 / 5000000000)))
noncomputable def ep13078 : ℝ := (1637016294017587 / 3125000000000000000)
noncomputable def em13078 : ℝ := (795947924576617 / 1562500000000000000)
noncomputable def bp13078 : ℝ := (1061767283239673463 / 2500000000000000000)
noncomputable def bm13078 : ℝ := (43485068634052658369 / 100000000000000000000)

theorem positive13078 :
    Eplus aL (agent13078.root+dsL) scalar13078.worldRadius world13078.frame
      agent13078.frame tp13078 ≤ -ep13078 := by
  apply positive_check (eT := (115693186026743978721 / 100000000000000000000)) (y := (3810891953014263711 / 10000000000000000000)) (u := (18298477133017764969 / 12500000000000000000))
  · norm_num [world13078, agent13078, scalar13078, tp13078, tm13078, ep13078, em13078, dsL]
  · norm_num [world13078, agent13078, scalar13078, tp13078, tm13078, ep13078, em13078, dsL]
  · norm_num [world13078, agent13078, scalar13078, tp13078, tm13078, ep13078, em13078, dsL]
  · norm_num [world13078, agent13078, scalar13078, tp13078, tm13078, ep13078, em13078, dsL]
  · norm_num [world13078, agent13078, scalar13078, tp13078, tm13078, ep13078, em13078, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13078, agent13078, tp13078, tm13078, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13078, agent13078, scalar13078, tp13078, tm13078, ep13078, em13078, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13078, agent13078, tp13078, tm13078, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13078, agent13078, scalar13078, tp13078, tm13078, ep13078, em13078, dsL]

theorem negative13078 :
    Eminus aL (agent13078.root+dsL) scalar13078.worldRadius world13078.frame
      agent13078.frame tm13078 ≤ -em13078 := by
  apply negative_check (lo := (34169316286537159333 / 50000000000000000000)) (hi := (68338632573074318667 / 100000000000000000000))
    (y := (-((17904089133960710423 / 25000000000000000000)))) (u := (48862323582779668309 / 100000000000000000000))
  · norm_num [world13078, agent13078, scalar13078, tp13078, tm13078, ep13078, em13078, dsL]
  · norm_num [world13078, agent13078, scalar13078, tp13078, tm13078, ep13078, em13078, dsL]
  · norm_num [world13078, agent13078, scalar13078, tp13078, tm13078, ep13078, em13078, dsL]
  · norm_num [world13078, agent13078, scalar13078, tp13078, tm13078, ep13078, em13078, dsL]
  · norm_num [world13078, agent13078, scalar13078, tp13078, tm13078, ep13078, em13078, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13078, agent13078, tp13078, tm13078, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13078, agent13078, tp13078, tm13078, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13078, agent13078, scalar13078, tp13078, tm13078, ep13078, em13078, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13078, agent13078, tp13078, tm13078, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13078, agent13078, scalar13078, tp13078, tm13078, ep13078, em13078, dsL]

theorem tails13078 :
    exp (-((13078:ℝ)*ep13078)) ≤ scalar13078.upperTail ∧
    exp (-((13078:ℝ)*em13078)) ≤ scalar13078.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13078:ℝ)) (by norm_num [ep13078]) ?_)
      (show bp13078^8 ≤ scalar13078.upperTail by norm_num [bp13078, scalar13078])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13078, bp13078, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13078:ℝ)) (by norm_num [em13078]) ?_)
      (show bm13078^8 ≤ scalar13078.lowerTail by norm_num [bm13078, scalar13078])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13078, bm13078, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13078 :
    agent13078.root+dsL+scalar13078.worldRadius < √(1/100/aL) ∧
    2*(agent13078.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13078, agent13078, scalar13078, tp13078, tm13078, ep13078, em13078, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13078, agent13078, scalar13078, tp13078, tm13078, ep13078, em13078, dsL]

noncomputable def master13078 : MasterCertificate 13078 world13078 agent13078 :=
  master scalar13078 dsL tp13078 tm13078 ep13078 em13078
    (by norm_num [dsL]) (by norm_num [tp13078]) (by norm_num [tm13078])
    (by norm_num [ep13078]) (by norm_num [em13078])
    positive13078 negative13078 tails13078.1 tails13078.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13078.1 tailGuards13078.2

theorem preserves13078 : master13078.toScalarCertificate = scalar13078 := rfl

noncomputable def tp13079 : ℝ := (2349152487 / 10000000000)
noncomputable def tm13079 : ℝ := (-((6134977639 / 10000000000)))
noncomputable def ep13079 : ℝ := (10477344369292509 / 20000000000000000000)
noncomputable def em13079 : ℝ := (10188506664540089 / 20000000000000000000)
noncomputable def bp13079 : ℝ := (8493276536316697011 / 20000000000000000000)
noncomputable def bm13079 : ℝ := (43480973183537275607 / 100000000000000000000)

theorem positive13079 :
    Eplus aL (agent13079.root+dsL) scalar13079.worldRadius world13079.frame
      agent13079.frame tp13079 ≤ -ep13079 := by
  apply positive_check (eT := (57846679497787064273 / 50000000000000000000)) (y := (19054789485049643423 / 50000000000000000000)) (u := (146388782407082433061 / 100000000000000000000))
  · norm_num [world13079, agent13079, scalar13079, tp13079, tm13079, ep13079, em13079, dsL]
  · norm_num [world13079, agent13079, scalar13079, tp13079, tm13079, ep13079, em13079, dsL]
  · norm_num [world13079, agent13079, scalar13079, tp13079, tm13079, ep13079, em13079, dsL]
  · norm_num [world13079, agent13079, scalar13079, tp13079, tm13079, ep13079, em13079, dsL]
  · norm_num [world13079, agent13079, scalar13079, tp13079, tm13079, ep13079, em13079, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13079, agent13079, tp13079, tm13079, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13079, agent13079, scalar13079, tp13079, tm13079, ep13079, em13079, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13079, agent13079, tp13079, tm13079, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13079, agent13079, scalar13079, tp13079, tm13079, ep13079, em13079, dsL]

theorem negative13079 :
    Eminus aL (agent13079.root+dsL) scalar13079.worldRadius world13079.frame
      agent13079.frame tm13079 ≤ -em13079 := by
  apply negative_check (lo := (6833851897717204393 / 10000000000000000000)) (hi := (68338518977172043931 / 100000000000000000000))
    (y := (-((14323254826177943011 / 20000000000000000000)))) (u := (1526948870242846983 / 3125000000000000000))
  · norm_num [world13079, agent13079, scalar13079, tp13079, tm13079, ep13079, em13079, dsL]
  · norm_num [world13079, agent13079, scalar13079, tp13079, tm13079, ep13079, em13079, dsL]
  · norm_num [world13079, agent13079, scalar13079, tp13079, tm13079, ep13079, em13079, dsL]
  · norm_num [world13079, agent13079, scalar13079, tp13079, tm13079, ep13079, em13079, dsL]
  · norm_num [world13079, agent13079, scalar13079, tp13079, tm13079, ep13079, em13079, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13079, agent13079, tp13079, tm13079, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13079, agent13079, tp13079, tm13079, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13079, agent13079, scalar13079, tp13079, tm13079, ep13079, em13079, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13079, agent13079, tp13079, tm13079, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13079, agent13079, scalar13079, tp13079, tm13079, ep13079, em13079, dsL]

theorem tails13079 :
    exp (-((13079:ℝ)*ep13079)) ≤ scalar13079.upperTail ∧
    exp (-((13079:ℝ)*em13079)) ≤ scalar13079.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13079:ℝ)) (by norm_num [ep13079]) ?_)
      (show bp13079^8 ≤ scalar13079.upperTail by norm_num [bp13079, scalar13079])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13079, bp13079, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13079:ℝ)) (by norm_num [em13079]) ?_)
      (show bm13079^8 ≤ scalar13079.lowerTail by norm_num [bm13079, scalar13079])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13079, bm13079, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13079 :
    agent13079.root+dsL+scalar13079.worldRadius < √(1/100/aL) ∧
    2*(agent13079.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13079, agent13079, scalar13079, tp13079, tm13079, ep13079, em13079, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13079, agent13079, scalar13079, tp13079, tm13079, ep13079, em13079, dsL]

noncomputable def master13079 : MasterCertificate 13079 world13079 agent13079 :=
  master scalar13079 dsL tp13079 tm13079 ep13079 em13079
    (by norm_num [dsL]) (by norm_num [tp13079]) (by norm_num [tm13079])
    (by norm_num [ep13079]) (by norm_num [em13079])
    positive13079 negative13079 tails13079.1 tails13079.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13079.1 tailGuards13079.2

theorem preserves13079 : master13079.toScalarCertificate = scalar13079 := rfl

noncomputable def tp13080 : ℝ := (1174648487 / 5000000000)
noncomputable def tm13080 : ℝ := (-((6135348833 / 10000000000)))
noncomputable def ep13080 : ℝ := (26195131572337371 / 50000000000000000000)
noncomputable def em13080 : ℝ := (10189172788945659 / 20000000000000000000)
noncomputable def bp13080 : ℝ := (42461143348447516077 / 100000000000000000000)
noncomputable def bm13080 : ℝ := (43475836912736588751 / 100000000000000000000)

theorem positive13080 :
    Eplus aL (agent13080.root+dsL) scalar13080.worldRadius world13080.frame
      agent13080.frame tp13080 ≤ -ep13080 := by
  apply positive_check (eT := (115694041882195126557 / 100000000000000000000)) (y := (38109524311202131141 / 100000000000000000000)) (u := (146388702392610277201 / 100000000000000000000))
  · norm_num [world13080, agent13080, scalar13080, tp13080, tm13080, ep13080, em13080, dsL]
  · norm_num [world13080, agent13080, scalar13080, tp13080, tm13080, ep13080, em13080, dsL]
  · norm_num [world13080, agent13080, scalar13080, tp13080, tm13080, ep13080, em13080, dsL]
  · norm_num [world13080, agent13080, scalar13080, tp13080, tm13080, ep13080, em13080, dsL]
  · norm_num [world13080, agent13080, scalar13080, tp13080, tm13080, ep13080, em13080, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13080, agent13080, tp13080, tm13080, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13080, agent13080, scalar13080, tp13080, tm13080, ep13080, em13080, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13080, agent13080, tp13080, tm13080, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13080, agent13080, scalar13080, tp13080, tm13080, ep13080, em13080, dsL]

theorem negative13080 :
    Eminus aL (agent13080.root+dsL) scalar13080.worldRadius world13080.frame
      agent13080.frame tm13080 ≤ -em13080 := by
  apply negative_check (lo := (13667498321508810853 / 20000000000000000000)) (hi := (34168745803772027133 / 50000000000000000000))
    (y := (-((447589569067422217 / 625000000000000000)))) (u := (1221582832296616861 / 2500000000000000000))
  · norm_num [world13080, agent13080, scalar13080, tp13080, tm13080, ep13080, em13080, dsL]
  · norm_num [world13080, agent13080, scalar13080, tp13080, tm13080, ep13080, em13080, dsL]
  · norm_num [world13080, agent13080, scalar13080, tp13080, tm13080, ep13080, em13080, dsL]
  · norm_num [world13080, agent13080, scalar13080, tp13080, tm13080, ep13080, em13080, dsL]
  · norm_num [world13080, agent13080, scalar13080, tp13080, tm13080, ep13080, em13080, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13080, agent13080, tp13080, tm13080, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13080, agent13080, tp13080, tm13080, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13080, agent13080, scalar13080, tp13080, tm13080, ep13080, em13080, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13080, agent13080, tp13080, tm13080, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13080, agent13080, scalar13080, tp13080, tm13080, ep13080, em13080, dsL]

theorem tails13080 :
    exp (-((13080:ℝ)*ep13080)) ≤ scalar13080.upperTail ∧
    exp (-((13080:ℝ)*em13080)) ≤ scalar13080.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13080:ℝ)) (by norm_num [ep13080]) ?_)
      (show bp13080^8 ≤ scalar13080.upperTail by norm_num [bp13080, scalar13080])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13080, bp13080, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13080:ℝ)) (by norm_num [em13080]) ?_)
      (show bm13080^8 ≤ scalar13080.lowerTail by norm_num [bm13080, scalar13080])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13080, bm13080, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13080 :
    agent13080.root+dsL+scalar13080.worldRadius < √(1/100/aL) ∧
    2*(agent13080.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13080, agent13080, scalar13080, tp13080, tm13080, ep13080, em13080, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13080, agent13080, scalar13080, tp13080, tm13080, ep13080, em13080, dsL]

noncomputable def master13080 : MasterCertificate 13080 world13080 agent13080 :=
  master scalar13080 dsL tp13080 tm13080 ep13080 em13080
    (by norm_num [dsL]) (by norm_num [tp13080]) (by norm_num [tm13080])
    (by norm_num [ep13080]) (by norm_num [em13080])
    positive13080 negative13080 tails13080.1 tails13080.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13080.1 tailGuards13080.2

theorem preserves13080 : master13080.toScalarCertificate = scalar13080 := rfl

noncomputable def tp13081 : ℝ := (1174685169 / 5000000000)
noncomputable def tm13081 : ℝ := (-((6135504449 / 10000000000)))
noncomputable def ep13081 : ℝ := (26196230489083991 / 50000000000000000000)
noncomputable def em13081 : ℝ := (50947727680077191 / 100000000000000000000)
noncomputable def bp13081 : ℝ := (21228418469422058507 / 50000000000000000000)
noncomputable def bm13081 : ℝ := (21735871781349533823 / 50000000000000000000)

theorem positive13081 :
    Eplus aL (agent13081.root+dsL) scalar13081.worldRadius world13081.frame
      agent13081.frame tp13081 ≤ -ep13081 := by
  apply positive_check (eT := (57847107098147751413 / 50000000000000000000)) (y := (762203653772580701 / 2000000000000000000)) (u := (1829870827324438289 / 1250000000000000000))
  · norm_num [world13081, agent13081, scalar13081, tp13081, tm13081, ep13081, em13081, dsL]
  · norm_num [world13081, agent13081, scalar13081, tp13081, tm13081, ep13081, em13081, dsL]
  · norm_num [world13081, agent13081, scalar13081, tp13081, tm13081, ep13081, em13081, dsL]
  · norm_num [world13081, agent13081, scalar13081, tp13081, tm13081, ep13081, em13081, dsL]
  · norm_num [world13081, agent13081, scalar13081, tp13081, tm13081, ep13081, em13081, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13081, agent13081, tp13081, tm13081, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13081, agent13081, scalar13081, tp13081, tm13081, ep13081, em13081, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13081, agent13081, tp13081, tm13081, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13081, agent13081, scalar13081, tp13081, tm13081, ep13081, em13081, dsL]

theorem negative13081 :
    Eminus aL (agent13081.root+dsL) scalar13081.worldRadius world13081.frame
      agent13081.frame tm13081 ≤ -em13081 := by
  apply negative_check (lo := (17084344591046776429 / 25000000000000000000)) (hi := (68337378364187105717 / 100000000000000000000))
    (y := (-((71614248633093680559 / 100000000000000000000)))) (u := (2443167678194861787 / 5000000000000000000))
  · norm_num [world13081, agent13081, scalar13081, tp13081, tm13081, ep13081, em13081, dsL]
  · norm_num [world13081, agent13081, scalar13081, tp13081, tm13081, ep13081, em13081, dsL]
  · norm_num [world13081, agent13081, scalar13081, tp13081, tm13081, ep13081, em13081, dsL]
  · norm_num [world13081, agent13081, scalar13081, tp13081, tm13081, ep13081, em13081, dsL]
  · norm_num [world13081, agent13081, scalar13081, tp13081, tm13081, ep13081, em13081, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13081, agent13081, tp13081, tm13081, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13081, agent13081, tp13081, tm13081, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13081, agent13081, scalar13081, tp13081, tm13081, ep13081, em13081, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13081, agent13081, tp13081, tm13081, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13081, agent13081, scalar13081, tp13081, tm13081, ep13081, em13081, dsL]

theorem tails13081 :
    exp (-((13081:ℝ)*ep13081)) ≤ scalar13081.upperTail ∧
    exp (-((13081:ℝ)*em13081)) ≤ scalar13081.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13081:ℝ)) (by norm_num [ep13081]) ?_)
      (show bp13081^8 ≤ scalar13081.upperTail by norm_num [bp13081, scalar13081])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13081, bp13081, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13081:ℝ)) (by norm_num [em13081]) ?_)
      (show bm13081^8 ≤ scalar13081.lowerTail by norm_num [bm13081, scalar13081])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13081, bm13081, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13081 :
    agent13081.root+dsL+scalar13081.worldRadius < √(1/100/aL) ∧
    2*(agent13081.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13081, agent13081, scalar13081, tp13081, tm13081, ep13081, em13081, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13081, agent13081, scalar13081, tp13081, tm13081, ep13081, em13081, dsL]

noncomputable def master13081 : MasterCertificate 13081 world13081 agent13081 :=
  master scalar13081 dsL tp13081 tm13081 ep13081 em13081
    (by norm_num [dsL]) (by norm_num [tp13081]) (by norm_num [tm13081])
    (by norm_num [ep13081]) (by norm_num [em13081])
    positive13081 negative13081 tails13081.1 tails13081.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13081.1 tailGuards13081.2

theorem preserves13081 : master13081.toScalarCertificate = scalar13081 := rfl

noncomputable def tp13082 : ℝ := (2349443619 / 10000000000)
noncomputable def tm13082 : ℝ := (-((766957499 / 1250000000)))
noncomputable def ep13082 : ℝ := (52394658083709673 / 100000000000000000000)
noncomputable def em13082 : ℝ := (10189918144976871 / 20000000000000000000)
noncomputable def bp13082 : ℝ := (21226265619042727059 / 50000000000000000000)
noncomputable def bm13082 : ℝ := (10866912721592430811 / 25000000000000000000)

theorem positive13082 :
    Eplus aL (agent13082.root+dsL) scalar13082.worldRadius world13082.frame
      agent13082.frame tp13082 ≤ -ep13082 := by
  apply positive_check (eT := (57847192973780653923 / 50000000000000000000)) (y := (38110839884339357121 / 100000000000000000000)) (u := (5855625130228917167 / 4000000000000000000))
  · norm_num [world13082, agent13082, scalar13082, tp13082, tm13082, ep13082, em13082, dsL]
  · norm_num [world13082, agent13082, scalar13082, tp13082, tm13082, ep13082, em13082, dsL]
  · norm_num [world13082, agent13082, scalar13082, tp13082, tm13082, ep13082, em13082, dsL]
  · norm_num [world13082, agent13082, scalar13082, tp13082, tm13082, ep13082, em13082, dsL]
  · norm_num [world13082, agent13082, scalar13082, tp13082, tm13082, ep13082, em13082, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13082, agent13082, tp13082, tm13082, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13082, agent13082, scalar13082, tp13082, tm13082, ep13082, em13082, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13082, agent13082, tp13082, tm13082, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13082, agent13082, scalar13082, tp13082, tm13082, ep13082, em13082, dsL]

theorem negative13082 :
    Eminus aL (agent13082.root+dsL) scalar13082.worldRadius world13082.frame
      agent13082.frame tm13082 ≤ -em13082 := by
  apply negative_check (lo := (68337265373633179467 / 100000000000000000000)) (hi := (17084316343408294867 / 25000000000000000000))
    (y := (-((71614165977855537201 / 100000000000000000000)))) (u := (48863393952035180263 / 100000000000000000000))
  · norm_num [world13082, agent13082, scalar13082, tp13082, tm13082, ep13082, em13082, dsL]
  · norm_num [world13082, agent13082, scalar13082, tp13082, tm13082, ep13082, em13082, dsL]
  · norm_num [world13082, agent13082, scalar13082, tp13082, tm13082, ep13082, em13082, dsL]
  · norm_num [world13082, agent13082, scalar13082, tp13082, tm13082, ep13082, em13082, dsL]
  · norm_num [world13082, agent13082, scalar13082, tp13082, tm13082, ep13082, em13082, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13082, agent13082, tp13082, tm13082, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13082, agent13082, tp13082, tm13082, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13082, agent13082, scalar13082, tp13082, tm13082, ep13082, em13082, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13082, agent13082, tp13082, tm13082, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13082, agent13082, scalar13082, tp13082, tm13082, ep13082, em13082, dsL]

theorem tails13082 :
    exp (-((13082:ℝ)*ep13082)) ≤ scalar13082.upperTail ∧
    exp (-((13082:ℝ)*em13082)) ≤ scalar13082.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13082:ℝ)) (by norm_num [ep13082]) ?_)
      (show bp13082^8 ≤ scalar13082.upperTail by norm_num [bp13082, scalar13082])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13082, bp13082, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13082:ℝ)) (by norm_num [em13082]) ?_)
      (show bm13082^8 ≤ scalar13082.lowerTail by norm_num [bm13082, scalar13082])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13082, bm13082, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13082 :
    agent13082.root+dsL+scalar13082.worldRadius < √(1/100/aL) ∧
    2*(agent13082.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13082, agent13082, scalar13082, tp13082, tm13082, ep13082, em13082, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13082, agent13082, scalar13082, tp13082, tm13082, ep13082, em13082, dsL]

noncomputable def master13082 : MasterCertificate 13082 world13082 agent13082 :=
  master scalar13082 dsL tp13082 tm13082 ep13082 em13082
    (by norm_num [dsL]) (by norm_num [tp13082]) (by norm_num [tm13082])
    (by norm_num [ep13082]) (by norm_num [em13082])
    positive13082 negative13082 tails13082.1 tails13082.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13082.1 tailGuards13082.2

theorem preserves13082 : master13082.toScalarCertificate = scalar13082 := rfl

noncomputable def tp13083 : ℝ := (234951689 / 1000000000)
noncomputable def tm13083 : ℝ := (-((6135815271 / 10000000000)))
noncomputable def ep13083 : ℝ := (26198426860787039 / 50000000000000000000)
noncomputable def em13083 : ℝ := (25475726210874749 / 50000000000000000000)
noncomputable def bp13083 : ℝ := (5306028344958602919 / 12500000000000000000)
noncomputable def bm13083 : ℝ := (339559057429831053 / 781250000000000000)

theorem positive13083 :
    Eplus aL (agent13083.root+dsL) scalar13083.worldRadius world13083.frame
      agent13083.frame tp13083 ≤ -ep13083 := by
  apply positive_check (eT := (28923639415004854831 / 25000000000000000000)) (y := (1190984291288088687 / 3125000000000000000)) (u := (146391590684864864623 / 100000000000000000000))
  · norm_num [world13083, agent13083, scalar13083, tp13083, tm13083, ep13083, em13083, dsL]
  · norm_num [world13083, agent13083, scalar13083, tp13083, tm13083, ep13083, em13083, dsL]
  · norm_num [world13083, agent13083, scalar13083, tp13083, tm13083, ep13083, em13083, dsL]
  · norm_num [world13083, agent13083, scalar13083, tp13083, tm13083, ep13083, em13083, dsL]
  · norm_num [world13083, agent13083, scalar13083, tp13083, tm13083, ep13083, em13083, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13083, agent13083, tp13083, tm13083, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13083, agent13083, scalar13083, tp13083, tm13083, ep13083, em13083, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13083, agent13083, tp13083, tm13083, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13083, agent13083, scalar13083, tp13083, tm13083, ep13083, em13083, dsL]

theorem negative13083 :
    Eminus aL (agent13083.root+dsL) scalar13083.worldRadius world13083.frame
      agent13083.frame tm13083 ≤ -em13083 := by
  apply negative_check (lo := (68337153445817265807 / 100000000000000000000)) (hi := (4271072090363579113 / 6250000000000000000))
    (y := (-((7161408153301627333 / 10000000000000000000)))) (u := (48863435214667084011 / 100000000000000000000))
  · norm_num [world13083, agent13083, scalar13083, tp13083, tm13083, ep13083, em13083, dsL]
  · norm_num [world13083, agent13083, scalar13083, tp13083, tm13083, ep13083, em13083, dsL]
  · norm_num [world13083, agent13083, scalar13083, tp13083, tm13083, ep13083, em13083, dsL]
  · norm_num [world13083, agent13083, scalar13083, tp13083, tm13083, ep13083, em13083, dsL]
  · norm_num [world13083, agent13083, scalar13083, tp13083, tm13083, ep13083, em13083, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13083, agent13083, tp13083, tm13083, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13083, agent13083, tp13083, tm13083, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13083, agent13083, scalar13083, tp13083, tm13083, ep13083, em13083, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13083, agent13083, tp13083, tm13083, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13083, agent13083, scalar13083, tp13083, tm13083, ep13083, em13083, dsL]

theorem tails13083 :
    exp (-((13083:ℝ)*ep13083)) ≤ scalar13083.upperTail ∧
    exp (-((13083:ℝ)*em13083)) ≤ scalar13083.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13083:ℝ)) (by norm_num [ep13083]) ?_)
      (show bp13083^8 ≤ scalar13083.upperTail by norm_num [bp13083, scalar13083])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13083, bp13083, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13083:ℝ)) (by norm_num [em13083]) ?_)
      (show bm13083^8 ≤ scalar13083.lowerTail by norm_num [bm13083, scalar13083])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13083, bm13083, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13083 :
    agent13083.root+dsL+scalar13083.worldRadius < √(1/100/aL) ∧
    2*(agent13083.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13083, agent13083, scalar13083, tp13083, tm13083, ep13083, em13083, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13083, agent13083, scalar13083, tp13083, tm13083, ep13083, em13083, dsL]

noncomputable def master13083 : MasterCertificate 13083 world13083 agent13083 :=
  master scalar13083 dsL tp13083 tm13083 ep13083 em13083
    (by norm_num [dsL]) (by norm_num [tp13083]) (by norm_num [tm13083])
    (by norm_num [ep13083]) (by norm_num [em13083])
    positive13083 negative13083 tails13083.1 tails13083.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13083.1 tailGuards13083.2

theorem preserves13083 : master13083.toScalarCertificate = scalar13083 := rfl

noncomputable def tp13084 : ℝ := (1174795039 / 5000000000)
noncomputable def tm13084 : ℝ := (-((6135970603 / 10000000000)))
noncomputable def ep13084 : ℝ := (10479809599897273 / 20000000000000000000)
noncomputable def em13084 : ℝ := (12738328206580949 / 25000000000000000000)
noncomputable def bp13084 : ℝ := (21221961714382465373 / 50000000000000000000)
noncomputable def bm13084 : ℝ := (347675751336474513 / 800000000000000000)

theorem positive13084 :
    Eplus aL (agent13084.root+dsL) scalar13084.worldRadius world13084.frame
      agent13084.frame tp13084 ≤ -ep13084 := by
  apply positive_check (eT := (57847364404837833199 / 50000000000000000000)) (y := (19056076888913316429 / 50000000000000000000)) (u := (146392551685289443387 / 100000000000000000000))
  · norm_num [world13084, agent13084, scalar13084, tp13084, tm13084, ep13084, em13084, dsL]
  · norm_num [world13084, agent13084, scalar13084, tp13084, tm13084, ep13084, em13084, dsL]
  · norm_num [world13084, agent13084, scalar13084, tp13084, tm13084, ep13084, em13084, dsL]
  · norm_num [world13084, agent13084, scalar13084, tp13084, tm13084, ep13084, em13084, dsL]
  · norm_num [world13084, agent13084, scalar13084, tp13084, tm13084, ep13084, em13084, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13084, agent13084, tp13084, tm13084, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13084, agent13084, scalar13084, tp13084, tm13084, ep13084, em13084, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13084, agent13084, tp13084, tm13084, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13084, agent13084, scalar13084, tp13084, tm13084, ep13084, em13084, dsL]

theorem negative13084 :
    Eminus aL (agent13084.root+dsL) scalar13084.worldRadius world13084.frame
      agent13084.frame tm13084 ≤ -em13084 := by
  apply negative_check (lo := (34168520618251025211 / 50000000000000000000)) (hi := (68337041236502050423 / 100000000000000000000))
    (y := (-((17903499554239204493 / 25000000000000000000)))) (u := (9772695185154555767 / 20000000000000000000))
  · norm_num [world13084, agent13084, scalar13084, tp13084, tm13084, ep13084, em13084, dsL]
  · norm_num [world13084, agent13084, scalar13084, tp13084, tm13084, ep13084, em13084, dsL]
  · norm_num [world13084, agent13084, scalar13084, tp13084, tm13084, ep13084, em13084, dsL]
  · norm_num [world13084, agent13084, scalar13084, tp13084, tm13084, ep13084, em13084, dsL]
  · norm_num [world13084, agent13084, scalar13084, tp13084, tm13084, ep13084, em13084, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13084, agent13084, tp13084, tm13084, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13084, agent13084, tp13084, tm13084, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13084, agent13084, scalar13084, tp13084, tm13084, ep13084, em13084, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13084, agent13084, tp13084, tm13084, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13084, agent13084, scalar13084, tp13084, tm13084, ep13084, em13084, dsL]

theorem tails13084 :
    exp (-((13084:ℝ)*ep13084)) ≤ scalar13084.upperTail ∧
    exp (-((13084:ℝ)*em13084)) ≤ scalar13084.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13084:ℝ)) (by norm_num [ep13084]) ?_)
      (show bp13084^8 ≤ scalar13084.upperTail by norm_num [bp13084, scalar13084])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13084, bp13084, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13084:ℝ)) (by norm_num [em13084]) ?_)
      (show bm13084^8 ≤ scalar13084.lowerTail by norm_num [bm13084, scalar13084])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13084, bm13084, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13084 :
    agent13084.root+dsL+scalar13084.worldRadius < √(1/100/aL) ∧
    2*(agent13084.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13084, agent13084, scalar13084, tp13084, tm13084, ep13084, em13084, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13084, agent13084, scalar13084, tp13084, tm13084, ep13084, em13084, dsL]

noncomputable def master13084 : MasterCertificate 13084 world13084 agent13084 :=
  master scalar13084 dsL tp13084 tm13084 ep13084 em13084
    (by norm_num [dsL]) (by norm_num [tp13084]) (by norm_num [tm13084])
    (by norm_num [ep13084]) (by norm_num [em13084])
    positive13084 negative13084 tails13084.1 tails13084.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13084.1 tailGuards13084.2

theorem preserves13084 : master13084.toScalarCertificate = scalar13084 := rfl

noncomputable def tp13085 : ℝ := (2349663361 / 10000000000)
noncomputable def tm13085 : ℝ := (-((6136125877 / 10000000000)))
noncomputable def ep13085 : ℝ := (52401241730191899 / 100000000000000000000)
noncomputable def em13085 : ℝ := (50955172730399189 / 100000000000000000000)
noncomputable def bp13085 : ℝ := (21219810340580012041 / 50000000000000000000)
noncomputable def bm13085 : ℝ := (10863844755421258097 / 25000000000000000000)

theorem positive13085 :
    Eplus aL (agent13085.root+dsL) scalar13085.worldRadius world13085.frame
      agent13085.frame tp13085 ≤ -ep13085 := by
  apply positive_check (eT := (14461862584283089917 / 12500000000000000000)) (y := (38112812105023336123 / 100000000000000000000)) (u := (73196757715221715139 / 50000000000000000000))
  · norm_num [world13085, agent13085, scalar13085, tp13085, tm13085, ep13085, em13085, dsL]
  · norm_num [world13085, agent13085, scalar13085, tp13085, tm13085, ep13085, em13085, dsL]
  · norm_num [world13085, agent13085, scalar13085, tp13085, tm13085, ep13085, em13085, dsL]
  · norm_num [world13085, agent13085, scalar13085, tp13085, tm13085, ep13085, em13085, dsL]
  · norm_num [world13085, agent13085, scalar13085, tp13085, tm13085, ep13085, em13085, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13085, agent13085, tp13085, tm13085, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13085, agent13085, scalar13085, tp13085, tm13085, ep13085, em13085, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13085, agent13085, tp13085, tm13085, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13085, agent13085, scalar13085, tp13085, tm13085, ep13085, em13085, dsL]

theorem negative13085 :
    Eminus aL (agent13085.root+dsL) scalar13085.worldRadius world13085.frame
      agent13085.frame tm13085 ≤ -em13085 := by
  apply negative_check (lo := (34168464608210741261 / 50000000000000000000)) (hi := (68336929216421482523 / 100000000000000000000))
    (y := (-((71613914931301332077 / 100000000000000000000)))) (u := (3053969788878496493 / 6250000000000000000))
  · norm_num [world13085, agent13085, scalar13085, tp13085, tm13085, ep13085, em13085, dsL]
  · norm_num [world13085, agent13085, scalar13085, tp13085, tm13085, ep13085, em13085, dsL]
  · norm_num [world13085, agent13085, scalar13085, tp13085, tm13085, ep13085, em13085, dsL]
  · norm_num [world13085, agent13085, scalar13085, tp13085, tm13085, ep13085, em13085, dsL]
  · norm_num [world13085, agent13085, scalar13085, tp13085, tm13085, ep13085, em13085, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13085, agent13085, tp13085, tm13085, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13085, agent13085, tp13085, tm13085, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13085, agent13085, scalar13085, tp13085, tm13085, ep13085, em13085, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13085, agent13085, tp13085, tm13085, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13085, agent13085, scalar13085, tp13085, tm13085, ep13085, em13085, dsL]

theorem tails13085 :
    exp (-((13085:ℝ)*ep13085)) ≤ scalar13085.upperTail ∧
    exp (-((13085:ℝ)*em13085)) ≤ scalar13085.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13085:ℝ)) (by norm_num [ep13085]) ?_)
      (show bp13085^8 ≤ scalar13085.upperTail by norm_num [bp13085, scalar13085])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13085, bp13085, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13085:ℝ)) (by norm_num [em13085]) ?_)
      (show bm13085^8 ≤ scalar13085.lowerTail by norm_num [bm13085, scalar13085])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13085, bm13085, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13085 :
    agent13085.root+dsL+scalar13085.worldRadius < √(1/100/aL) ∧
    2*(agent13085.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13085, agent13085, scalar13085, tp13085, tm13085, ep13085, em13085, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13085, agent13085, scalar13085, tp13085, tm13085, ep13085, em13085, dsL]

noncomputable def master13085 : MasterCertificate 13085 world13085 agent13085 :=
  master scalar13085 dsL tp13085 tm13085 ep13085 em13085
    (by norm_num [dsL]) (by norm_num [tp13085]) (by norm_num [tm13085])
    (by norm_num [ep13085]) (by norm_num [em13085])
    positive13085 negative13085 tails13085.1 tails13085.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13085.1 tailGuards13085.2

theorem preserves13085 : master13085.toScalarCertificate = scalar13085 := rfl

noncomputable def tp13086 : ℝ := (587434121 / 2500000000)
noncomputable def tm13086 : ℝ := (-((767035123 / 1250000000)))
noncomputable def ep13086 : ℝ := (52403433997959037 / 100000000000000000000)
noncomputable def em13086 : ℝ := (50957031290662417 / 100000000000000000000)
noncomputable def bp13086 : ℝ := (5304414894061785957 / 12500000000000000000)
noncomputable def bm13086 : ℝ := (43451290264286154187 / 100000000000000000000)

theorem positive13086 :
    Eplus aL (agent13086.root+dsL) scalar13086.worldRadius world13086.frame
      agent13086.frame tp13086 ≤ -ep13086 := by
  apply positive_check (eT := (28923767855832972543 / 25000000000000000000)) (y := (38113468058314910017 / 100000000000000000000)) (u := (146394475706676025343 / 100000000000000000000))
  · norm_num [world13086, agent13086, scalar13086, tp13086, tm13086, ep13086, em13086, dsL]
  · norm_num [world13086, agent13086, scalar13086, tp13086, tm13086, ep13086, em13086, dsL]
  · norm_num [world13086, agent13086, scalar13086, tp13086, tm13086, ep13086, em13086, dsL]
  · norm_num [world13086, agent13086, scalar13086, tp13086, tm13086, ep13086, em13086, dsL]
  · norm_num [world13086, agent13086, scalar13086, tp13086, tm13086, ep13086, em13086, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13086, agent13086, tp13086, tm13086, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13086, agent13086, scalar13086, tp13086, tm13086, ep13086, em13086, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13086, agent13086, tp13086, tm13086, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13086, agent13086, scalar13086, tp13086, tm13086, ep13086, em13086, dsL]

theorem negative13086 :
    Eminus aL (agent13086.root+dsL) scalar13086.worldRadius world13086.frame
      agent13086.frame tm13086 ≤ -em13086 := by
  apply negative_check (lo := (3416840892383063903 / 5000000000000000000)) (hi := (68336817847661278061 / 100000000000000000000))
    (y := (-((71613830785766149013 / 100000000000000000000)))) (u := (48863557738540813623 / 100000000000000000000))
  · norm_num [world13086, agent13086, scalar13086, tp13086, tm13086, ep13086, em13086, dsL]
  · norm_num [world13086, agent13086, scalar13086, tp13086, tm13086, ep13086, em13086, dsL]
  · norm_num [world13086, agent13086, scalar13086, tp13086, tm13086, ep13086, em13086, dsL]
  · norm_num [world13086, agent13086, scalar13086, tp13086, tm13086, ep13086, em13086, dsL]
  · norm_num [world13086, agent13086, scalar13086, tp13086, tm13086, ep13086, em13086, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13086, agent13086, tp13086, tm13086, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13086, agent13086, tp13086, tm13086, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13086, agent13086, scalar13086, tp13086, tm13086, ep13086, em13086, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13086, agent13086, tp13086, tm13086, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13086, agent13086, scalar13086, tp13086, tm13086, ep13086, em13086, dsL]

theorem tails13086 :
    exp (-((13086:ℝ)*ep13086)) ≤ scalar13086.upperTail ∧
    exp (-((13086:ℝ)*em13086)) ≤ scalar13086.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13086:ℝ)) (by norm_num [ep13086]) ?_)
      (show bp13086^8 ≤ scalar13086.upperTail by norm_num [bp13086, scalar13086])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13086, bp13086, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13086:ℝ)) (by norm_num [em13086]) ?_)
      (show bm13086^8 ≤ scalar13086.lowerTail by norm_num [bm13086, scalar13086])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13086, bm13086, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13086 :
    agent13086.root+dsL+scalar13086.worldRadius < √(1/100/aL) ∧
    2*(agent13086.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13086, agent13086, scalar13086, tp13086, tm13086, ep13086, em13086, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13086, agent13086, scalar13086, tp13086, tm13086, ep13086, em13086, dsL]

noncomputable def master13086 : MasterCertificate 13086 world13086 agent13086 :=
  master scalar13086 dsL tp13086 tm13086 ep13086 em13086
    (by norm_num [dsL]) (by norm_num [tp13086]) (by norm_num [tm13086])
    (by norm_num [ep13086]) (by norm_num [em13086])
    positive13086 negative13086 tails13086.1 tails13086.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13086.1 tailGuards13086.2

theorem preserves13086 : master13086.toScalarCertificate = scalar13086 := rfl

noncomputable def tp13087 : ℝ := (2349809597 / 10000000000)
noncomputable def tm13087 : ℝ := (-((613643617 / 1000000000)))
noncomputable def ep13087 : ℝ := (52405625054688653 / 100000000000000000000)
noncomputable def em13087 : ℝ := (25479444356575397 / 50000000000000000000)
noncomputable def bp13087 : ℝ := (8486203733573846311 / 20000000000000000000)
noncomputable def bm13087 : ℝ := (43447202498393469323 / 100000000000000000000)

theorem positive13087 :
    Eplus aL (agent13087.root+dsL) scalar13087.worldRadius world13087.frame
      agent13087.frame tp13087 ≤ -ep13087 := by
  apply positive_check (eT := (115695242133607963961 / 100000000000000000000)) (y := (19057062075671782963 / 50000000000000000000)) (u := (7319771809688815761 / 5000000000000000000))
  · norm_num [world13087, agent13087, scalar13087, tp13087, tm13087, ep13087, em13087, dsL]
  · norm_num [world13087, agent13087, scalar13087, tp13087, tm13087, ep13087, em13087, dsL]
  · norm_num [world13087, agent13087, scalar13087, tp13087, tm13087, ep13087, em13087, dsL]
  · norm_num [world13087, agent13087, scalar13087, tp13087, tm13087, ep13087, em13087, dsL]
  · norm_num [world13087, agent13087, scalar13087, tp13087, tm13087, ep13087, em13087, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13087, agent13087, tp13087, tm13087, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13087, agent13087, scalar13087, tp13087, tm13087, ep13087, em13087, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13087, agent13087, tp13087, tm13087, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13087, agent13087, scalar13087, tp13087, tm13087, ep13087, em13087, dsL]

theorem negative13087 :
    Eminus aL (agent13087.root+dsL) scalar13087.worldRadius world13087.frame
      agent13087.frame tm13087 ≤ -em13087 := by
  apply negative_check (lo := (6833670608725616143 / 10000000000000000000)) (hi := (68336706087256161431 / 100000000000000000000))
    (y := (-((35806873865818809019 / 50000000000000000000)))) (u := (9772719664351943123 / 20000000000000000000))
  · norm_num [world13087, agent13087, scalar13087, tp13087, tm13087, ep13087, em13087, dsL]
  · norm_num [world13087, agent13087, scalar13087, tp13087, tm13087, ep13087, em13087, dsL]
  · norm_num [world13087, agent13087, scalar13087, tp13087, tm13087, ep13087, em13087, dsL]
  · norm_num [world13087, agent13087, scalar13087, tp13087, tm13087, ep13087, em13087, dsL]
  · norm_num [world13087, agent13087, scalar13087, tp13087, tm13087, ep13087, em13087, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13087, agent13087, tp13087, tm13087, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13087, agent13087, tp13087, tm13087, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13087, agent13087, scalar13087, tp13087, tm13087, ep13087, em13087, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13087, agent13087, tp13087, tm13087, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13087, agent13087, scalar13087, tp13087, tm13087, ep13087, em13087, dsL]

theorem tails13087 :
    exp (-((13087:ℝ)*ep13087)) ≤ scalar13087.upperTail ∧
    exp (-((13087:ℝ)*em13087)) ≤ scalar13087.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13087:ℝ)) (by norm_num [ep13087]) ?_)
      (show bp13087^8 ≤ scalar13087.upperTail by norm_num [bp13087, scalar13087])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13087, bp13087, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13087:ℝ)) (by norm_num [em13087]) ?_)
      (show bm13087^8 ≤ scalar13087.lowerTail by norm_num [bm13087, scalar13087])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13087, bm13087, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13087 :
    agent13087.root+dsL+scalar13087.worldRadius < √(1/100/aL) ∧
    2*(agent13087.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13087, agent13087, scalar13087, tp13087, tm13087, ep13087, em13087, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13087, agent13087, scalar13087, tp13087, tm13087, ep13087, em13087, dsL]

noncomputable def master13087 : MasterCertificate 13087 world13087 agent13087 :=
  master scalar13087 dsL tp13087 tm13087 ep13087 em13087
    (by norm_num [dsL]) (by norm_num [tp13087]) (by norm_num [tm13087])
    (by norm_num [ep13087]) (by norm_num [em13087])
    positive13087 negative13087 tails13087.1 tails13087.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13087.1 tailGuards13087.2

theorem preserves13087 : master13087.toScalarCertificate = scalar13087 := rfl

noncomputable def tp13088 : ℝ := (2349882741 / 10000000000)
noncomputable def tm13088 : ℝ := (-((3068295557 / 5000000000)))
noncomputable def ep13088 : ℝ := (26203907635606307 / 50000000000000000000)
noncomputable def em13088 : ℝ := (50960745385813141 / 100000000000000000000)
noncomputable def bp13088 : ℝ := (21213359484926830967 / 50000000000000000000)
noncomputable def bm13088 : ℝ := (43443115448258259657 / 100000000000000000000)

theorem positive13088 :
    Eplus aL (agent13088.root+dsL) scalar13088.worldRadius world13088.frame
      agent13088.frame tp13088 ≤ -ep13088 := by
  apply positive_check (eT := (115695413099398113471 / 100000000000000000000)) (y := (38114780998005938061 / 100000000000000000000)) (u := (18299549723808865451 / 12500000000000000000))
  · norm_num [world13088, agent13088, scalar13088, tp13088, tm13088, ep13088, em13088, dsL]
  · norm_num [world13088, agent13088, scalar13088, tp13088, tm13088, ep13088, em13088, dsL]
  · norm_num [world13088, agent13088, scalar13088, tp13088, tm13088, ep13088, em13088, dsL]
  · norm_num [world13088, agent13088, scalar13088, tp13088, tm13088, ep13088, em13088, dsL]
  · norm_num [world13088, agent13088, scalar13088, tp13088, tm13088, ep13088, em13088, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13088, agent13088, tp13088, tm13088, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13088, agent13088, scalar13088, tp13088, tm13088, ep13088, em13088, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13088, agent13088, tp13088, tm13088, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13088, agent13088, scalar13088, tp13088, tm13088, ep13088, em13088, dsL]

theorem negative13088 :
    Eminus aL (agent13088.root+dsL) scalar13088.worldRadius world13088.frame
      agent13088.frame tm13088 ≤ -em13088 := by
  apply negative_check (lo := (34168297648086575023 / 50000000000000000000)) (hi := (68336595296173150047 / 100000000000000000000))
    (y := (-((71613662939675476273 / 100000000000000000000)))) (u := (9772727950836214277 / 20000000000000000000))
  · norm_num [world13088, agent13088, scalar13088, tp13088, tm13088, ep13088, em13088, dsL]
  · norm_num [world13088, agent13088, scalar13088, tp13088, tm13088, ep13088, em13088, dsL]
  · norm_num [world13088, agent13088, scalar13088, tp13088, tm13088, ep13088, em13088, dsL]
  · norm_num [world13088, agent13088, scalar13088, tp13088, tm13088, ep13088, em13088, dsL]
  · norm_num [world13088, agent13088, scalar13088, tp13088, tm13088, ep13088, em13088, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13088, agent13088, tp13088, tm13088, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13088, agent13088, tp13088, tm13088, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13088, agent13088, scalar13088, tp13088, tm13088, ep13088, em13088, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13088, agent13088, tp13088, tm13088, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13088, agent13088, scalar13088, tp13088, tm13088, ep13088, em13088, dsL]

theorem tails13088 :
    exp (-((13088:ℝ)*ep13088)) ≤ scalar13088.upperTail ∧
    exp (-((13088:ℝ)*em13088)) ≤ scalar13088.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13088:ℝ)) (by norm_num [ep13088]) ?_)
      (show bp13088^8 ≤ scalar13088.upperTail by norm_num [bp13088, scalar13088])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13088, bp13088, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13088:ℝ)) (by norm_num [em13088]) ?_)
      (show bm13088^8 ≤ scalar13088.lowerTail by norm_num [bm13088, scalar13088])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13088, bm13088, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13088 :
    agent13088.root+dsL+scalar13088.worldRadius < √(1/100/aL) ∧
    2*(agent13088.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13088, agent13088, scalar13088, tp13088, tm13088, ep13088, em13088, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13088, agent13088, scalar13088, tp13088, tm13088, ep13088, em13088, dsL]

noncomputable def master13088 : MasterCertificate 13088 world13088 agent13088 :=
  master scalar13088 dsL tp13088 tm13088 ep13088 em13088
    (by norm_num [dsL]) (by norm_num [tp13088]) (by norm_num [tm13088])
    (by norm_num [ep13088]) (by norm_num [em13088])
    positive13088 negative13088 tails13088.1 tails13088.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13088.1 tailGuards13088.2

theorem preserves13088 : master13088.toScalarCertificate = scalar13088 := rfl

noncomputable def tp13089 : ℝ := (587488941 / 2500000000)
noncomputable def tm13089 : ℝ := (-((6136745989 / 10000000000)))
noncomputable def ep13089 : ℝ := (10482000989097963 / 20000000000000000000)
noncomputable def em13089 : ℝ := (12740650376742849 / 25000000000000000000)
noncomputable def bp13089 : ℝ := (21211209925810993559 / 50000000000000000000)
noncomputable def bm13089 : ℝ := (173756115891689157 / 400000000000000000)

theorem positive13089 :
    Eplus aL (agent13089.root+dsL) scalar13089.worldRadius world13089.frame
      agent13089.frame tp13089 ≤ -ep13089 := by
  apply positive_check (eT := (115695583229668348021 / 100000000000000000000)) (y := (38115436255184507307 / 100000000000000000000)) (u := (146397357066519471611 / 100000000000000000000))
  · norm_num [world13089, agent13089, scalar13089, tp13089, tm13089, ep13089, em13089, dsL]
  · norm_num [world13089, agent13089, scalar13089, tp13089, tm13089, ep13089, em13089, dsL]
  · norm_num [world13089, agent13089, scalar13089, tp13089, tm13089, ep13089, em13089, dsL]
  · norm_num [world13089, agent13089, scalar13089, tp13089, tm13089, ep13089, em13089, dsL]
  · norm_num [world13089, agent13089, scalar13089, tp13089, tm13089, ep13089, em13089, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13089, agent13089, tp13089, tm13089, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13089, agent13089, scalar13089, tp13089, tm13089, ep13089, em13089, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13089, agent13089, tp13089, tm13089, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13089, agent13089, scalar13089, tp13089, tm13089, ep13089, em13089, dsL]

theorem negative13089 :
    Eminus aL (agent13089.root+dsL) scalar13089.worldRadius world13089.frame
      agent13089.frame tm13089 ≤ -em13089 := by
  apply negative_check (lo := (34168242370440685131 / 50000000000000000000)) (hi := (68336484740881370263 / 100000000000000000000))
    (y := (-((71613578647262711343 / 100000000000000000000)))) (u := (12215920235634836069 / 25000000000000000000))
  · norm_num [world13089, agent13089, scalar13089, tp13089, tm13089, ep13089, em13089, dsL]
  · norm_num [world13089, agent13089, scalar13089, tp13089, tm13089, ep13089, em13089, dsL]
  · norm_num [world13089, agent13089, scalar13089, tp13089, tm13089, ep13089, em13089, dsL]
  · norm_num [world13089, agent13089, scalar13089, tp13089, tm13089, ep13089, em13089, dsL]
  · norm_num [world13089, agent13089, scalar13089, tp13089, tm13089, ep13089, em13089, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13089, agent13089, tp13089, tm13089, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13089, agent13089, tp13089, tm13089, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13089, agent13089, scalar13089, tp13089, tm13089, ep13089, em13089, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13089, agent13089, tp13089, tm13089, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13089, agent13089, scalar13089, tp13089, tm13089, ep13089, em13089, dsL]

theorem tails13089 :
    exp (-((13089:ℝ)*ep13089)) ≤ scalar13089.upperTail ∧
    exp (-((13089:ℝ)*em13089)) ≤ scalar13089.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13089:ℝ)) (by norm_num [ep13089]) ?_)
      (show bp13089^8 ≤ scalar13089.upperTail by norm_num [bp13089, scalar13089])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13089, bp13089, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13089:ℝ)) (by norm_num [em13089]) ?_)
      (show bm13089^8 ≤ scalar13089.lowerTail by norm_num [bm13089, scalar13089])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13089, bm13089, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13089 :
    agent13089.root+dsL+scalar13089.worldRadius < √(1/100/aL) ∧
    2*(agent13089.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13089, agent13089, scalar13089, tp13089, tm13089, ep13089, em13089, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13089, agent13089, scalar13089, tp13089, tm13089, ep13089, em13089, dsL]

noncomputable def master13089 : MasterCertificate 13089 world13089 agent13089 :=
  master scalar13089 dsL tp13089 tm13089 ep13089 em13089
    (by norm_num [dsL]) (by norm_num [tp13089]) (by norm_num [tm13089])
    (by norm_num [ep13089]) (by norm_num [em13089])
    positive13089 negative13089 tails13089.1 tails13089.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13089.1 tailGuards13089.2

theorem preserves13089 : master13089.toScalarCertificate = scalar13089 := rfl

noncomputable def tp13090 : ℝ := (2350099843 / 10000000000)
noncomputable def tm13090 : ℝ := (-((3068558021 / 5000000000)))
noncomputable def ep13090 : ℝ := (26206766480440461 / 50000000000000000000)
noncomputable def em13090 : ℝ := (101931839147019 / 200000000000000000)
noncomputable def bp13090 : ℝ := (21208596024625023021 / 50000000000000000000)
noncomputable def bm13090 : ℝ := (10858475920515521007 / 25000000000000000000)

theorem positive13090 :
    Eplus aL (agent13090.root+dsL) scalar13090.worldRadius world13090.frame
      agent13090.frame tp13090 ≤ -ep13090 := by
  apply positive_check (eT := (14462032926273759489 / 12500000000000000000)) (y := (38115379556001512871 / 100000000000000000000)) (u := (29279454812087524267 / 20000000000000000000))
  · norm_num [world13090, agent13090, scalar13090, tp13090, tm13090, ep13090, em13090, dsL]
  · norm_num [world13090, agent13090, scalar13090, tp13090, tm13090, ep13090, em13090, dsL]
  · norm_num [world13090, agent13090, scalar13090, tp13090, tm13090, ep13090, em13090, dsL]
  · norm_num [world13090, agent13090, scalar13090, tp13090, tm13090, ep13090, em13090, dsL]
  · norm_num [world13090, agent13090, scalar13090, tp13090, tm13090, ep13090, em13090, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13090, agent13090, tp13090, tm13090, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13090, agent13090, scalar13090, tp13090, tm13090, ep13090, em13090, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13090, agent13090, tp13090, tm13090, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13090, agent13090, scalar13090, tp13090, tm13090, ep13090, em13090, dsL]

theorem negative13090 :
    Eminus aL (agent13090.root+dsL) scalar13090.worldRadius world13090.frame
      agent13090.frame tm13090 ≤ -em13090 := by
  apply negative_check (lo := (34167730940743399369 / 50000000000000000000)) (hi := (68335461881486798739 / 100000000000000000000))
    (y := (-((17902908452630779031 / 25000000000000000000)))) (u := (48864631270599768047 / 100000000000000000000))
  · norm_num [world13090, agent13090, scalar13090, tp13090, tm13090, ep13090, em13090, dsL]
  · norm_num [world13090, agent13090, scalar13090, tp13090, tm13090, ep13090, em13090, dsL]
  · norm_num [world13090, agent13090, scalar13090, tp13090, tm13090, ep13090, em13090, dsL]
  · norm_num [world13090, agent13090, scalar13090, tp13090, tm13090, ep13090, em13090, dsL]
  · norm_num [world13090, agent13090, scalar13090, tp13090, tm13090, ep13090, em13090, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13090, agent13090, tp13090, tm13090, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13090, agent13090, tp13090, tm13090, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13090, agent13090, scalar13090, tp13090, tm13090, ep13090, em13090, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13090, agent13090, tp13090, tm13090, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13090, agent13090, scalar13090, tp13090, tm13090, ep13090, em13090, dsL]

theorem tails13090 :
    exp (-((13090:ℝ)*ep13090)) ≤ scalar13090.upperTail ∧
    exp (-((13090:ℝ)*em13090)) ≤ scalar13090.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13090:ℝ)) (by norm_num [ep13090]) ?_)
      (show bp13090^8 ≤ scalar13090.upperTail by norm_num [bp13090, scalar13090])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13090, bp13090, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13090:ℝ)) (by norm_num [em13090]) ?_)
      (show bm13090^8 ≤ scalar13090.lowerTail by norm_num [bm13090, scalar13090])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13090, bm13090, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13090 :
    agent13090.root+dsL+scalar13090.worldRadius < √(1/100/aL) ∧
    2*(agent13090.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13090, agent13090, scalar13090, tp13090, tm13090, ep13090, em13090, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13090, agent13090, scalar13090, tp13090, tm13090, ep13090, em13090, dsL]

noncomputable def master13090 : MasterCertificate 13090 world13090 agent13090 :=
  master scalar13090 dsL tp13090 tm13090 ep13090 em13090
    (by norm_num [dsL]) (by norm_num [tp13090]) (by norm_num [tm13090])
    (by norm_num [ep13090]) (by norm_num [em13090])
    positive13090 negative13090 tails13090.1 tails13090.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13090.1 tailGuards13090.2

theorem preserves13090 : master13090.toScalarCertificate = scalar13090 := rfl

noncomputable def tp13091 : ℝ := (1175086413 / 5000000000)
noncomputable def tm13091 : ℝ := (-((1227454159 / 2000000000)))
noncomputable def ep13091 : ℝ := (52415718938515629 / 100000000000000000000)
noncomputable def em13091 : ℝ := (50967772306280867 / 100000000000000000000)
noncomputable def bp13091 : ℝ := (8482579185335058243 / 20000000000000000000)
noncomputable def bm13091 : ℝ := (21714909999425700717 / 50000000000000000000)

theorem positive13091 :
    Eplus aL (agent13091.root+dsL) scalar13091.worldRadius world13091.frame
      agent13091.frame tp13091 ≤ -ep13091 := by
  apply positive_check (eT := (115696433309424805883 / 100000000000000000000)) (y := (2382252170201826101 / 6250000000000000000)) (u := (146398233210541533563 / 100000000000000000000))
  · norm_num [world13091, agent13091, scalar13091, tp13091, tm13091, ep13091, em13091, dsL]
  · norm_num [world13091, agent13091, scalar13091, tp13091, tm13091, ep13091, em13091, dsL]
  · norm_num [world13091, agent13091, scalar13091, tp13091, tm13091, ep13091, em13091, dsL]
  · norm_num [world13091, agent13091, scalar13091, tp13091, tm13091, ep13091, em13091, dsL]
  · norm_num [world13091, agent13091, scalar13091, tp13091, tm13091, ep13091, em13091, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13091, agent13091, tp13091, tm13091, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13091, agent13091, scalar13091, tp13091, tm13091, ep13091, em13091, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13091, agent13091, tp13091, tm13091, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13091, agent13091, scalar13091, tp13091, tm13091, ep13091, em13091, dsL]

theorem negative13091 :
    Eminus aL (agent13091.root+dsL) scalar13091.worldRadius world13091.frame
      agent13091.frame tm13091 ≤ -em13091 := by
  apply negative_check (lo := (34167675875285354899 / 50000000000000000000)) (hi := (68335351750570709799 / 100000000000000000000))
    (y := (-((716115487944625479 / 1000000000000000000)))) (u := (12216168203350486131 / 25000000000000000000))
  · norm_num [world13091, agent13091, scalar13091, tp13091, tm13091, ep13091, em13091, dsL]
  · norm_num [world13091, agent13091, scalar13091, tp13091, tm13091, ep13091, em13091, dsL]
  · norm_num [world13091, agent13091, scalar13091, tp13091, tm13091, ep13091, em13091, dsL]
  · norm_num [world13091, agent13091, scalar13091, tp13091, tm13091, ep13091, em13091, dsL]
  · norm_num [world13091, agent13091, scalar13091, tp13091, tm13091, ep13091, em13091, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13091, agent13091, tp13091, tm13091, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13091, agent13091, tp13091, tm13091, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13091, agent13091, scalar13091, tp13091, tm13091, ep13091, em13091, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13091, agent13091, tp13091, tm13091, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13091, agent13091, scalar13091, tp13091, tm13091, ep13091, em13091, dsL]

theorem tails13091 :
    exp (-((13091:ℝ)*ep13091)) ≤ scalar13091.upperTail ∧
    exp (-((13091:ℝ)*em13091)) ≤ scalar13091.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13091:ℝ)) (by norm_num [ep13091]) ?_)
      (show bp13091^8 ≤ scalar13091.upperTail by norm_num [bp13091, scalar13091])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13091, bp13091, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13091:ℝ)) (by norm_num [em13091]) ?_)
      (show bm13091^8 ≤ scalar13091.lowerTail by norm_num [bm13091, scalar13091])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13091, bm13091, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13091 :
    agent13091.root+dsL+scalar13091.worldRadius < √(1/100/aL) ∧
    2*(agent13091.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13091, agent13091, scalar13091, tp13091, tm13091, ep13091, em13091, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13091, agent13091, scalar13091, tp13091, tm13091, ep13091, em13091, dsL]

noncomputable def master13091 : MasterCertificate 13091 world13091 agent13091 :=
  master scalar13091 dsL tp13091 tm13091 ep13091 em13091
    (by norm_num [dsL]) (by norm_num [tp13091]) (by norm_num [tm13091])
    (by norm_num [ep13091]) (by norm_num [em13091])
    positive13091 negative13091 tails13091.1 tails13091.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13091.1 tailGuards13091.2

theorem preserves13091 : master13091.toScalarCertificate = scalar13091 := rfl

noncomputable def tp13092 : ℝ := (235024577 / 1000000000)
noncomputable def tm13092 : ℝ := (-((3068712803 / 5000000000)))
noncomputable def ep13092 : ℝ := (10483580999349449 / 20000000000000000000)
noncomputable def em13092 : ℝ := (50969625081663699 / 100000000000000000000)
noncomputable def bp13092 : ℝ := (1696343998061067001 / 4000000000000000000)
noncomputable def bm13092 : ℝ := (43425736468168138207 / 100000000000000000000)

theorem positive13092 :
    Eplus aL (agent13092.root+dsL) scalar13092.worldRadius world13092.frame
      agent13092.frame tp13092 ≤ -ep13092 := by
  apply positive_check (eT := (115696602961742954997 / 100000000000000000000)) (y := (19058344764200957669 / 50000000000000000000)) (u := (146399191836883898277 / 100000000000000000000))
  · norm_num [world13092, agent13092, scalar13092, tp13092, tm13092, ep13092, em13092, dsL]
  · norm_num [world13092, agent13092, scalar13092, tp13092, tm13092, ep13092, em13092, dsL]
  · norm_num [world13092, agent13092, scalar13092, tp13092, tm13092, ep13092, em13092, dsL]
  · norm_num [world13092, agent13092, scalar13092, tp13092, tm13092, ep13092, em13092, dsL]
  · norm_num [world13092, agent13092, scalar13092, tp13092, tm13092, ep13092, em13092, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13092, agent13092, tp13092, tm13092, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13092, agent13092, scalar13092, tp13092, tm13092, ep13092, em13092, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13092, agent13092, tp13092, tm13092, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13092, agent13092, scalar13092, tp13092, tm13092, ep13092, em13092, dsL]

theorem negative13092 :
    Eminus aL (agent13092.root+dsL) scalar13092.worldRadius world13092.frame
      agent13092.frame tm13092 ≤ -em13092 := by
  apply negative_check (lo := (683352413170600679 / 1000000000000000000)) (hi := (68335241317060067901 / 100000000000000000000))
    (y := (-((14322293067319029141 / 20000000000000000000)))) (u := (48864713594832805303 / 100000000000000000000))
  · norm_num [world13092, agent13092, scalar13092, tp13092, tm13092, ep13092, em13092, dsL]
  · norm_num [world13092, agent13092, scalar13092, tp13092, tm13092, ep13092, em13092, dsL]
  · norm_num [world13092, agent13092, scalar13092, tp13092, tm13092, ep13092, em13092, dsL]
  · norm_num [world13092, agent13092, scalar13092, tp13092, tm13092, ep13092, em13092, dsL]
  · norm_num [world13092, agent13092, scalar13092, tp13092, tm13092, ep13092, em13092, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13092, agent13092, tp13092, tm13092, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13092, agent13092, tp13092, tm13092, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13092, agent13092, scalar13092, tp13092, tm13092, ep13092, em13092, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13092, agent13092, tp13092, tm13092, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13092, agent13092, scalar13092, tp13092, tm13092, ep13092, em13092, dsL]

theorem tails13092 :
    exp (-((13092:ℝ)*ep13092)) ≤ scalar13092.upperTail ∧
    exp (-((13092:ℝ)*em13092)) ≤ scalar13092.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13092:ℝ)) (by norm_num [ep13092]) ?_)
      (show bp13092^8 ≤ scalar13092.upperTail by norm_num [bp13092, scalar13092])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13092, bp13092, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13092:ℝ)) (by norm_num [em13092]) ?_)
      (show bm13092^8 ≤ scalar13092.lowerTail by norm_num [bm13092, scalar13092])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13092, bm13092, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13092 :
    agent13092.root+dsL+scalar13092.worldRadius < √(1/100/aL) ∧
    2*(agent13092.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13092, agent13092, scalar13092, tp13092, tm13092, ep13092, em13092, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13092, agent13092, scalar13092, tp13092, tm13092, ep13092, em13092, dsL]

noncomputable def master13092 : MasterCertificate 13092 world13092 agent13092 :=
  master scalar13092 dsL tp13092 tm13092 ep13092 em13092
    (by norm_num [dsL]) (by norm_num [tp13092]) (by norm_num [tm13092])
    (by norm_num [ep13092]) (by norm_num [em13092])
    positive13092 negative13092 tails13092.1 tails13092.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13092.1 tailGuards13092.2

theorem preserves13092 : master13092.toScalarCertificate = scalar13092 := rfl

noncomputable def tp13093 : ℝ := (2350318737 / 10000000000)
noncomputable def tm13093 : ℝ := (-((6137580037 / 10000000000)))
noncomputable def ep13093 : ℝ := (52420089257616517 / 100000000000000000000)
noncomputable def em13093 : ℝ := (10194295244056829 / 20000000000000000000)
noncomputable def bp13093 : ℝ := (5300538178392178381 / 12500000000000000000)
noncomputable def bm13093 : ℝ := (43421654283480957989 / 100000000000000000000)

theorem positive13093 :
    Eplus aL (agent13093.root+dsL) scalar13093.worldRadius world13093.frame
      agent13093.frame tp13093 ≤ -ep13093 := by
  apply positive_check (eT := (23139354562431446283 / 20000000000000000000)) (y := (19058672522983755771 / 50000000000000000000)) (u := (29280030302489539489 / 20000000000000000000))
  · norm_num [world13093, agent13093, scalar13093, tp13093, tm13093, ep13093, em13093, dsL]
  · norm_num [world13093, agent13093, scalar13093, tp13093, tm13093, ep13093, em13093, dsL]
  · norm_num [world13093, agent13093, scalar13093, tp13093, tm13093, ep13093, em13093, dsL]
  · norm_num [world13093, agent13093, scalar13093, tp13093, tm13093, ep13093, em13093, dsL]
  · norm_num [world13093, agent13093, scalar13093, tp13093, tm13093, ep13093, em13093, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13093, agent13093, tp13093, tm13093, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13093, agent13093, scalar13093, tp13093, tm13093, ep13093, em13093, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13093, agent13093, tp13093, tm13093, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13093, agent13093, scalar13093, tp13093, tm13093, ep13093, em13093, dsL]

theorem negative13093 :
    Eminus aL (agent13093.root+dsL) scalar13093.worldRadius world13093.frame
      agent13093.frame tm13093 ≤ -em13093 := by
  apply negative_check (lo := (34167566218864307293 / 50000000000000000000)) (hi := (68335132437728614587 / 100000000000000000000))
    (y := (-((71611378561826716599 / 100000000000000000000)))) (u := (24432377998546633997 / 50000000000000000000))
  · norm_num [world13093, agent13093, scalar13093, tp13093, tm13093, ep13093, em13093, dsL]
  · norm_num [world13093, agent13093, scalar13093, tp13093, tm13093, ep13093, em13093, dsL]
  · norm_num [world13093, agent13093, scalar13093, tp13093, tm13093, ep13093, em13093, dsL]
  · norm_num [world13093, agent13093, scalar13093, tp13093, tm13093, ep13093, em13093, dsL]
  · norm_num [world13093, agent13093, scalar13093, tp13093, tm13093, ep13093, em13093, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13093, agent13093, tp13093, tm13093, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13093, agent13093, tp13093, tm13093, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13093, agent13093, scalar13093, tp13093, tm13093, ep13093, em13093, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13093, agent13093, tp13093, tm13093, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13093, agent13093, scalar13093, tp13093, tm13093, ep13093, em13093, dsL]

theorem tails13093 :
    exp (-((13093:ℝ)*ep13093)) ≤ scalar13093.upperTail ∧
    exp (-((13093:ℝ)*em13093)) ≤ scalar13093.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13093:ℝ)) (by norm_num [ep13093]) ?_)
      (show bp13093^8 ≤ scalar13093.upperTail by norm_num [bp13093, scalar13093])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13093, bp13093, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13093:ℝ)) (by norm_num [em13093]) ?_)
      (show bm13093^8 ≤ scalar13093.lowerTail by norm_num [bm13093, scalar13093])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13093, bm13093, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13093 :
    agent13093.root+dsL+scalar13093.worldRadius < √(1/100/aL) ∧
    2*(agent13093.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13093, agent13093, scalar13093, tp13093, tm13093, ep13093, em13093, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13093, agent13093, scalar13093, tp13093, tm13093, ep13093, em13093, dsL]

noncomputable def master13093 : MasterCertificate 13093 world13093 agent13093 :=
  master scalar13093 dsL tp13093 tm13093 ep13093 em13093
    (by norm_num [dsL]) (by norm_num [tp13093]) (by norm_num [tm13093])
    (by norm_num [ep13093]) (by norm_num [em13093])
    positive13093 negative13093 tails13093.1 tails13093.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13093.1 tailGuards13093.2

theorem preserves13093 : master13093.toScalarCertificate = scalar13093 := rfl

noncomputable def tp13094 : ℝ := (2350391667 / 10000000000)
noncomputable def tm13094 : ℝ := (-((383608411 / 625000000)))
noncomputable def ep13094 : ℝ := (52422272790901763 / 100000000000000000000)
noncomputable def em13094 : ℝ := (50973326669000291 / 100000000000000000000)
noncomputable def bp13094 : ℝ := (10600002902758401101 / 25000000000000000000)
noncomputable def bm13094 : ℝ := (10854393192969108307 / 25000000000000000000)

theorem positive13094 :
    Eplus aL (agent13094.root+dsL) scalar13094.worldRadius world13094.frame
      agent13094.frame tp13094 ≤ -ep13094 := by
  apply positive_check (eT := (57848471215003946503 / 50000000000000000000)) (y := (19059000091274777397 / 50000000000000000000)) (u := (146401110636538205199 / 100000000000000000000))
  · norm_num [world13094, agent13094, scalar13094, tp13094, tm13094, ep13094, em13094, dsL]
  · norm_num [world13094, agent13094, scalar13094, tp13094, tm13094, ep13094, em13094, dsL]
  · norm_num [world13094, agent13094, scalar13094, tp13094, tm13094, ep13094, em13094, dsL]
  · norm_num [world13094, agent13094, scalar13094, tp13094, tm13094, ep13094, em13094, dsL]
  · norm_num [world13094, agent13094, scalar13094, tp13094, tm13094, ep13094, em13094, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13094, agent13094, tp13094, tm13094, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13094, agent13094, scalar13094, tp13094, tm13094, ep13094, em13094, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13094, agent13094, tp13094, tm13094, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13094, agent13094, scalar13094, tp13094, tm13094, ep13094, em13094, dsL]

theorem negative13094 :
    Eminus aL (agent13094.root+dsL) scalar13094.worldRadius world13094.frame
      agent13094.frame tm13094 ≤ -em13094 := by
  apply negative_check (lo := (34167511521913650619 / 50000000000000000000)) (hi := (68335023043827301239 / 100000000000000000000))
    (y := (-((71611293282591300303 / 100000000000000000000)))) (u := (48864797668601338923 / 100000000000000000000))
  · norm_num [world13094, agent13094, scalar13094, tp13094, tm13094, ep13094, em13094, dsL]
  · norm_num [world13094, agent13094, scalar13094, tp13094, tm13094, ep13094, em13094, dsL]
  · norm_num [world13094, agent13094, scalar13094, tp13094, tm13094, ep13094, em13094, dsL]
  · norm_num [world13094, agent13094, scalar13094, tp13094, tm13094, ep13094, em13094, dsL]
  · norm_num [world13094, agent13094, scalar13094, tp13094, tm13094, ep13094, em13094, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13094, agent13094, tp13094, tm13094, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13094, agent13094, tp13094, tm13094, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13094, agent13094, scalar13094, tp13094, tm13094, ep13094, em13094, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13094, agent13094, tp13094, tm13094, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13094, agent13094, scalar13094, tp13094, tm13094, ep13094, em13094, dsL]

theorem tails13094 :
    exp (-((13094:ℝ)*ep13094)) ≤ scalar13094.upperTail ∧
    exp (-((13094:ℝ)*em13094)) ≤ scalar13094.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13094:ℝ)) (by norm_num [ep13094]) ?_)
      (show bp13094^8 ≤ scalar13094.upperTail by norm_num [bp13094, scalar13094])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13094, bp13094, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13094:ℝ)) (by norm_num [em13094]) ?_)
      (show bm13094^8 ≤ scalar13094.lowerTail by norm_num [bm13094, scalar13094])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13094, bm13094, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13094 :
    agent13094.root+dsL+scalar13094.worldRadius < √(1/100/aL) ∧
    2*(agent13094.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13094, agent13094, scalar13094, tp13094, tm13094, ep13094, em13094, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13094, agent13094, scalar13094, tp13094, tm13094, ep13094, em13094, dsL]

noncomputable def master13094 : MasterCertificate 13094 world13094 agent13094 :=
  master scalar13094 dsL tp13094 tm13094 ep13094 em13094
    (by norm_num [dsL]) (by norm_num [tp13094]) (by norm_num [tm13094])
    (by norm_num [ep13094]) (by norm_num [em13094])
    positive13094 negative13094 tails13094.1 tails13094.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13094.1 tailGuards13094.2

theorem preserves13094 : master13094.toScalarCertificate = scalar13094 := rfl

noncomputable def tp13095 : ℝ := (1175232239 / 5000000000)
noncomputable def tm13095 : ℝ := (-((6137888973 / 10000000000)))
noncomputable def ep13095 : ℝ := (26212227340287733 / 50000000000000000000)
noncomputable def em13095 : ℝ := (25487587792103429 / 50000000000000000000)
noncomputable def bp13095 : ℝ := (4239571913889475489 / 10000000000000000000)
noncomputable def bm13095 : ℝ := (5426686566604485067 / 12500000000000000000)

theorem positive13095 :
    Eplus aL (agent13095.root+dsL) scalar13095.worldRadius world13095.frame
      agent13095.frame tp13095 ≤ -ep13095 := by
  apply positive_check (eT := (115697111226802090993 / 100000000000000000000)) (y := (7623730741929447317 / 20000000000000000000)) (u := (18300258426324238441 / 12500000000000000000))
  · norm_num [world13095, agent13095, scalar13095, tp13095, tm13095, ep13095, em13095, dsL]
  · norm_num [world13095, agent13095, scalar13095, tp13095, tm13095, ep13095, em13095, dsL]
  · norm_num [world13095, agent13095, scalar13095, tp13095, tm13095, ep13095, em13095, dsL]
  · norm_num [world13095, agent13095, scalar13095, tp13095, tm13095, ep13095, em13095, dsL]
  · norm_num [world13095, agent13095, scalar13095, tp13095, tm13095, ep13095, em13095, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13095, agent13095, tp13095, tm13095, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13095, agent13095, scalar13095, tp13095, tm13095, ep13095, em13095, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13095, agent13095, tp13095, tm13095, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13095, agent13095, scalar13095, tp13095, tm13095, ep13095, em13095, dsL]

theorem negative13095 :
    Eminus aL (agent13095.root+dsL) scalar13095.worldRadius world13095.frame
      agent13095.frame tm13095 ≤ -em13095 := by
  apply negative_check (lo := (6833491419512954123 / 10000000000000000000)) (hi := (68334914195129541231 / 100000000000000000000))
    (y := (-((8951400907141463177 / 12500000000000000000)))) (u := (48864839704786194357 / 100000000000000000000))
  · norm_num [world13095, agent13095, scalar13095, tp13095, tm13095, ep13095, em13095, dsL]
  · norm_num [world13095, agent13095, scalar13095, tp13095, tm13095, ep13095, em13095, dsL]
  · norm_num [world13095, agent13095, scalar13095, tp13095, tm13095, ep13095, em13095, dsL]
  · norm_num [world13095, agent13095, scalar13095, tp13095, tm13095, ep13095, em13095, dsL]
  · norm_num [world13095, agent13095, scalar13095, tp13095, tm13095, ep13095, em13095, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13095, agent13095, tp13095, tm13095, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13095, agent13095, tp13095, tm13095, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13095, agent13095, scalar13095, tp13095, tm13095, ep13095, em13095, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13095, agent13095, tp13095, tm13095, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13095, agent13095, scalar13095, tp13095, tm13095, ep13095, em13095, dsL]

theorem tails13095 :
    exp (-((13095:ℝ)*ep13095)) ≤ scalar13095.upperTail ∧
    exp (-((13095:ℝ)*em13095)) ≤ scalar13095.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13095:ℝ)) (by norm_num [ep13095]) ?_)
      (show bp13095^8 ≤ scalar13095.upperTail by norm_num [bp13095, scalar13095])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13095, bp13095, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13095:ℝ)) (by norm_num [em13095]) ?_)
      (show bm13095^8 ≤ scalar13095.lowerTail by norm_num [bm13095, scalar13095])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13095, bm13095, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13095 :
    agent13095.root+dsL+scalar13095.worldRadius < √(1/100/aL) ∧
    2*(agent13095.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13095, agent13095, scalar13095, tp13095, tm13095, ep13095, em13095, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13095, agent13095, scalar13095, tp13095, tm13095, ep13095, em13095, dsL]

noncomputable def master13095 : MasterCertificate 13095 world13095 agent13095 :=
  master scalar13095 dsL tp13095 tm13095 ep13095 em13095
    (by norm_num [dsL]) (by norm_num [tp13095]) (by norm_num [tm13095])
    (by norm_num [ep13095]) (by norm_num [em13095])
    positive13095 negative13095 tails13095.1 tails13095.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13095.1 tailGuards13095.2

theorem preserves13095 : master13095.toScalarCertificate = scalar13095 := rfl

noncomputable def tp13096 : ℝ := (2350537283 / 10000000000)
noncomputable def tm13096 : ℝ := (-((1534510849 / 2500000000)))
noncomputable def ep13096 : ℝ := (26213317867456413 / 50000000000000000000)
noncomputable def em13096 : ℝ := (50977023753977717 / 100000000000000000000)
noncomputable def bp13096 : ℝ := (21195713724880655897 / 50000000000000000000)
noncomputable def bm13096 : ℝ := (21704706503153717199 / 50000000000000000000)

theorem positive13096 :
    Eplus aL (agent13096.root+dsL) scalar13096.worldRadius world13096.frame
      agent13096.frame tp13096 ≤ -ep13096 := by
  apply positive_check (eT := (2892432000338812857 / 2500000000000000000)) (y := (38119307344664284721 / 100000000000000000000)) (u := (146403024348899624109 / 100000000000000000000))
  · norm_num [world13096, agent13096, scalar13096, tp13096, tm13096, ep13096, em13096, dsL]
  · norm_num [world13096, agent13096, scalar13096, tp13096, tm13096, ep13096, em13096, dsL]
  · norm_num [world13096, agent13096, scalar13096, tp13096, tm13096, ep13096, em13096, dsL]
  · norm_num [world13096, agent13096, scalar13096, tp13096, tm13096, ep13096, em13096, dsL]
  · norm_num [world13096, agent13096, scalar13096, tp13096, tm13096, ep13096, em13096, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13096, agent13096, tp13096, tm13096, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13096, agent13096, scalar13096, tp13096, tm13096, ep13096, em13096, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13096, agent13096, tp13096, tm13096, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13096, agent13096, scalar13096, tp13096, tm13096, ep13096, em13096, dsL]

theorem negative13096 :
    Eminus aL (agent13096.root+dsL) scalar13096.worldRadius world13096.frame
      agent13096.frame tm13096 ≤ -em13096 := by
  apply negative_check (lo := (68334805179495496809 / 100000000000000000000)) (hi := (6833480517949549681 / 10000000000000000000))
    (y := (-((35805561031064344353 / 50000000000000000000)))) (u := (12216220333801397119 / 25000000000000000000))
  · norm_num [world13096, agent13096, scalar13096, tp13096, tm13096, ep13096, em13096, dsL]
  · norm_num [world13096, agent13096, scalar13096, tp13096, tm13096, ep13096, em13096, dsL]
  · norm_num [world13096, agent13096, scalar13096, tp13096, tm13096, ep13096, em13096, dsL]
  · norm_num [world13096, agent13096, scalar13096, tp13096, tm13096, ep13096, em13096, dsL]
  · norm_num [world13096, agent13096, scalar13096, tp13096, tm13096, ep13096, em13096, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13096, agent13096, tp13096, tm13096, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13096, agent13096, tp13096, tm13096, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13096, agent13096, scalar13096, tp13096, tm13096, ep13096, em13096, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13096, agent13096, tp13096, tm13096, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13096, agent13096, scalar13096, tp13096, tm13096, ep13096, em13096, dsL]

theorem tails13096 :
    exp (-((13096:ℝ)*ep13096)) ≤ scalar13096.upperTail ∧
    exp (-((13096:ℝ)*em13096)) ≤ scalar13096.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13096:ℝ)) (by norm_num [ep13096]) ?_)
      (show bp13096^8 ≤ scalar13096.upperTail by norm_num [bp13096, scalar13096])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13096, bp13096, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13096:ℝ)) (by norm_num [em13096]) ?_)
      (show bm13096^8 ≤ scalar13096.lowerTail by norm_num [bm13096, scalar13096])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13096, bm13096, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13096 :
    agent13096.root+dsL+scalar13096.worldRadius < √(1/100/aL) ∧
    2*(agent13096.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13096, agent13096, scalar13096, tp13096, tm13096, ep13096, em13096, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13096, agent13096, scalar13096, tp13096, tm13096, ep13096, em13096, dsL]

noncomputable def master13096 : MasterCertificate 13096 world13096 agent13096 :=
  master scalar13096 dsL tp13096 tm13096 ep13096 em13096
    (by norm_num [dsL]) (by norm_num [tp13096]) (by norm_num [tm13096])
    (by norm_num [ep13096]) (by norm_num [em13096])
    positive13096 negative13096 tails13096.1 tails13096.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13096.1 tailGuards13096.2

theorem preserves13096 : master13096.toScalarCertificate = scalar13096 := rfl

noncomputable def tp13097 : ℝ := (2350610077 / 10000000000)
noncomputable def tm13097 : ℝ := (-((1534549389 / 2500000000)))
noncomputable def ep13097 : ℝ := (52428815912795821 / 100000000000000000000)
noncomputable def em13097 : ℝ := (12744717769876529 / 25000000000000000000)
noncomputable def bp13097 : ℝ := (5298392071518660819 / 12500000000000000000)
noncomputable def bm13097 : ℝ := (5425666782811958099 / 12500000000000000000)

theorem positive13097 :
    Eplus aL (agent13097.root+dsL) scalar13097.worldRadius world13097.frame
      agent13097.frame tp13097 ≤ -ep13097 := by
  apply positive_check (eT := (115697448754383331729 / 100000000000000000000)) (y := (119124878762091741 / 312500000000000000)) (u := (73201990810840219231 / 50000000000000000000))
  · norm_num [world13097, agent13097, scalar13097, tp13097, tm13097, ep13097, em13097, dsL]
  · norm_num [world13097, agent13097, scalar13097, tp13097, tm13097, ep13097, em13097, dsL]
  · norm_num [world13097, agent13097, scalar13097, tp13097, tm13097, ep13097, em13097, dsL]
  · norm_num [world13097, agent13097, scalar13097, tp13097, tm13097, ep13097, em13097, dsL]
  · norm_num [world13097, agent13097, scalar13097, tp13097, tm13097, ep13097, em13097, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13097, agent13097, tp13097, tm13097, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13097, agent13097, scalar13097, tp13097, tm13097, ep13097, em13097, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13097, agent13097, tp13097, tm13097, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13097, agent13097, scalar13097, tp13097, tm13097, ep13097, em13097, dsL]

theorem negative13097 :
    Eminus aL (agent13097.root+dsL) scalar13097.worldRadius world13097.frame
      agent13097.frame tm13097 ≤ -em13097 := by
  apply negative_check (lo := (68334697221940546667 / 100000000000000000000)) (hi := (17083674305485136667 / 25000000000000000000))
    (y := (-((1432220701829669637 / 2000000000000000000)))) (u := (48864923833326645711 / 100000000000000000000))
  · norm_num [world13097, agent13097, scalar13097, tp13097, tm13097, ep13097, em13097, dsL]
  · norm_num [world13097, agent13097, scalar13097, tp13097, tm13097, ep13097, em13097, dsL]
  · norm_num [world13097, agent13097, scalar13097, tp13097, tm13097, ep13097, em13097, dsL]
  · norm_num [world13097, agent13097, scalar13097, tp13097, tm13097, ep13097, em13097, dsL]
  · norm_num [world13097, agent13097, scalar13097, tp13097, tm13097, ep13097, em13097, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13097, agent13097, tp13097, tm13097, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13097, agent13097, tp13097, tm13097, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13097, agent13097, scalar13097, tp13097, tm13097, ep13097, em13097, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13097, agent13097, tp13097, tm13097, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13097, agent13097, scalar13097, tp13097, tm13097, ep13097, em13097, dsL]

theorem tails13097 :
    exp (-((13097:ℝ)*ep13097)) ≤ scalar13097.upperTail ∧
    exp (-((13097:ℝ)*em13097)) ≤ scalar13097.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13097:ℝ)) (by norm_num [ep13097]) ?_)
      (show bp13097^8 ≤ scalar13097.upperTail by norm_num [bp13097, scalar13097])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13097, bp13097, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13097:ℝ)) (by norm_num [em13097]) ?_)
      (show bm13097^8 ≤ scalar13097.lowerTail by norm_num [bm13097, scalar13097])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13097, bm13097, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13097 :
    agent13097.root+dsL+scalar13097.worldRadius < √(1/100/aL) ∧
    2*(agent13097.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13097, agent13097, scalar13097, tp13097, tm13097, ep13097, em13097, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13097, agent13097, scalar13097, tp13097, tm13097, ep13097, em13097, dsL]

noncomputable def master13097 : MasterCertificate 13097 world13097 agent13097 :=
  master scalar13097 dsL tp13097 tm13097 ep13097 em13097
    (by norm_num [dsL]) (by norm_num [tp13097]) (by norm_num [tm13097])
    (by norm_num [ep13097]) (by norm_num [em13097])
    positive13097 negative13097 tails13097.1 tails13097.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13097.1 tailGuards13097.2

theorem preserves13097 : master13097.toScalarCertificate = scalar13097 := rfl

noncomputable def tp13098 : ℝ := (470136563 / 2000000000)
noncomputable def tm13098 : ℝ := (-((6138351613 / 10000000000)))
noncomputable def ep13098 : ℝ := (52430994451824001 / 100000000000000000000)
noncomputable def em13098 : ℝ := (25490358437825969 / 50000000000000000000)
noncomputable def bp13098 : ℝ := (4238284703507920141 / 10000000000000000000)
noncomputable def bm13098 : ℝ := (43401256788241089823 / 100000000000000000000)

theorem positive13098 :
    Eplus aL (agent13098.root+dsL) scalar13098.worldRadius world13098.frame
      agent13098.frame tp13098 ≤ -ep13098 := by
  apply positive_check (eT := (28924404281582824239 / 25000000000000000000)) (y := (19060307275667774937 / 50000000000000000000)) (u := (73202469075754748657 / 50000000000000000000))
  · norm_num [world13098, agent13098, scalar13098, tp13098, tm13098, ep13098, em13098, dsL]
  · norm_num [world13098, agent13098, scalar13098, tp13098, tm13098, ep13098, em13098, dsL]
  · norm_num [world13098, agent13098, scalar13098, tp13098, tm13098, ep13098, em13098, dsL]
  · norm_num [world13098, agent13098, scalar13098, tp13098, tm13098, ep13098, em13098, dsL]
  · norm_num [world13098, agent13098, scalar13098, tp13098, tm13098, ep13098, em13098, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13098, agent13098, tp13098, tm13098, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13098, agent13098, scalar13098, tp13098, tm13098, ep13098, em13098, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13098, agent13098, tp13098, tm13098, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13098, agent13098, scalar13098, tp13098, tm13098, ep13098, em13098, dsL]

theorem negative13098 :
    Eminus aL (agent13098.root+dsL) scalar13098.worldRadius world13098.frame
      agent13098.frame tm13098 ≤ -em13098 := by
  apply negative_check (lo := (1708364741105799339 / 2500000000000000000)) (hi := (68334589644231973561 / 100000000000000000000))
    (y := (-((71610947748044344549 / 100000000000000000000)))) (u := (4886496651365029279 / 10000000000000000000))
  · norm_num [world13098, agent13098, scalar13098, tp13098, tm13098, ep13098, em13098, dsL]
  · norm_num [world13098, agent13098, scalar13098, tp13098, tm13098, ep13098, em13098, dsL]
  · norm_num [world13098, agent13098, scalar13098, tp13098, tm13098, ep13098, em13098, dsL]
  · norm_num [world13098, agent13098, scalar13098, tp13098, tm13098, ep13098, em13098, dsL]
  · norm_num [world13098, agent13098, scalar13098, tp13098, tm13098, ep13098, em13098, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13098, agent13098, tp13098, tm13098, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13098, agent13098, tp13098, tm13098, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13098, agent13098, scalar13098, tp13098, tm13098, ep13098, em13098, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13098, agent13098, tp13098, tm13098, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13098, agent13098, scalar13098, tp13098, tm13098, ep13098, em13098, dsL]

theorem tails13098 :
    exp (-((13098:ℝ)*ep13098)) ≤ scalar13098.upperTail ∧
    exp (-((13098:ℝ)*em13098)) ≤ scalar13098.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13098:ℝ)) (by norm_num [ep13098]) ?_)
      (show bp13098^8 ≤ scalar13098.upperTail by norm_num [bp13098, scalar13098])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13098, bp13098, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13098:ℝ)) (by norm_num [em13098]) ?_)
      (show bm13098^8 ≤ scalar13098.lowerTail by norm_num [bm13098, scalar13098])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13098, bm13098, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13098 :
    agent13098.root+dsL+scalar13098.worldRadius < √(1/100/aL) ∧
    2*(agent13098.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13098, agent13098, scalar13098, tp13098, tm13098, ep13098, em13098, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13098, agent13098, scalar13098, tp13098, tm13098, ep13098, em13098, dsL]

noncomputable def master13098 : MasterCertificate 13098 world13098 agent13098 :=
  master scalar13098 dsL tp13098 tm13098 ep13098 em13098
    (by norm_num [dsL]) (by norm_num [tp13098]) (by norm_num [tm13098])
    (by norm_num [ep13098]) (by norm_num [em13098])
    positive13098 negative13098 tails13098.1 tails13098.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13098.1 tailGuards13098.2

theorem preserves13098 : master13098.toScalarCertificate = scalar13098 := rfl

noncomputable def tp13099 : ℝ := (2350755553 / 10000000000)
noncomputable def tm13099 : ℝ := (-((613850577 / 1000000000)))
noncomputable def ep13099 : ℝ := (52433172295079833 / 100000000000000000000)
noncomputable def em13099 : ℝ := (50982562072957597 / 100000000000000000000)
noncomputable def bp13099 : ℝ := (42378558184091336647 / 100000000000000000000)
noncomputable def bm13099 : ℝ := (43397179922287025167 / 100000000000000000000)

theorem positive13099 :
    Eplus aL (agent13099.root+dsL) scalar13099.worldRadius world13099.frame
      agent13099.frame tp13099 ≤ -ep13099 := by
  apply positive_check (eT := (11569778553130553243 / 10000000000000000000)) (y := (4765158494829922699 / 12500000000000000000)) (u := (29281178955038774139 / 20000000000000000000))
  · norm_num [world13099, agent13099, scalar13099, tp13099, tm13099, ep13099, em13099, dsL]
  · norm_num [world13099, agent13099, scalar13099, tp13099, tm13099, ep13099, em13099, dsL]
  · norm_num [world13099, agent13099, scalar13099, tp13099, tm13099, ep13099, em13099, dsL]
  · norm_num [world13099, agent13099, scalar13099, tp13099, tm13099, ep13099, em13099, dsL]
  · norm_num [world13099, agent13099, scalar13099, tp13099, tm13099, ep13099, em13099, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13099, agent13099, tp13099, tm13099, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13099, agent13099, scalar13099, tp13099, tm13099, ep13099, em13099, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13099, agent13099, tp13099, tm13099, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13099, agent13099, scalar13099, tp13099, tm13099, ep13099, em13099, dsL]

theorem negative13099 :
    Eminus aL (agent13099.root+dsL) scalar13099.worldRadius world13099.frame
      agent13099.frame tm13099 ≤ -em13099 := by
  apply negative_check (lo := (34167240792947991963 / 50000000000000000000)) (hi := (68334481585895983927 / 100000000000000000000))
    (y := (-((17902715414403727649 / 25000000000000000000)))) (u := (48865008581727915441 / 100000000000000000000))
  · norm_num [world13099, agent13099, scalar13099, tp13099, tm13099, ep13099, em13099, dsL]
  · norm_num [world13099, agent13099, scalar13099, tp13099, tm13099, ep13099, em13099, dsL]
  · norm_num [world13099, agent13099, scalar13099, tp13099, tm13099, ep13099, em13099, dsL]
  · norm_num [world13099, agent13099, scalar13099, tp13099, tm13099, ep13099, em13099, dsL]
  · norm_num [world13099, agent13099, scalar13099, tp13099, tm13099, ep13099, em13099, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13099, agent13099, tp13099, tm13099, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13099, agent13099, tp13099, tm13099, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13099, agent13099, scalar13099, tp13099, tm13099, ep13099, em13099, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13099, agent13099, tp13099, tm13099, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13099, agent13099, scalar13099, tp13099, tm13099, ep13099, em13099, dsL]

theorem tails13099 :
    exp (-((13099:ℝ)*ep13099)) ≤ scalar13099.upperTail ∧
    exp (-((13099:ℝ)*em13099)) ≤ scalar13099.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13099:ℝ)) (by norm_num [ep13099]) ?_)
      (show bp13099^8 ≤ scalar13099.upperTail by norm_num [bp13099, scalar13099])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13099, bp13099, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13099:ℝ)) (by norm_num [em13099]) ?_)
      (show bm13099^8 ≤ scalar13099.lowerTail by norm_num [bm13099, scalar13099])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13099, bm13099, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13099 :
    agent13099.root+dsL+scalar13099.worldRadius < √(1/100/aL) ∧
    2*(agent13099.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13099, agent13099, scalar13099, tp13099, tm13099, ep13099, em13099, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13099, agent13099, scalar13099, tp13099, tm13099, ep13099, em13099, dsL]

noncomputable def master13099 : MasterCertificate 13099 world13099 agent13099 :=
  master scalar13099 dsL tp13099 tm13099 ep13099 em13099
    (by norm_num [dsL]) (by norm_num [tp13099]) (by norm_num [tm13099])
    (by norm_num [ep13099]) (by norm_num [em13099])
    positive13099 negative13099 tails13099.1 tails13099.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13099.1 tailGuards13099.2

theorem preserves13099 : master13099.toScalarCertificate = scalar13099 := rfl

end BstLean.Part268
