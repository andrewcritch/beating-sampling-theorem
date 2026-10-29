import BstLean.Part261Checker
import BstLean.Part281Scalar7
namespace BstLean.Part281
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12034 : ℝ := (2361286107 / 10000000000)
noncomputable def tm12034 : ℝ := (-((382054369 / 625000000)))
noncomputable def ep12034 : ℝ := (2712706777097243 / 5000000000000000000)
noncomputable def em12034 : ℝ := (52341893045713663 / 100000000000000000000)
noncomputable def bp12034 : ℝ := (11053620164196383179 / 25000000000000000000)
noncomputable def bm12034 : ℝ := (22752387371277022169 / 50000000000000000000)

theorem positive12034 :
    Eplus aL (agent12034.root+dsL) scalar12034.worldRadius world12034.frame
      agent12034.frame tp12034 ≤ -ep12034 := by
  apply positive_check (eT := (116186761503480390767 / 100000000000000000000)) (y := (39552036681446992701 / 100000000000000000000)) (u := (7425784081003182509 / 5000000000000000000))
  · norm_num [world12034, agent12034, scalar12034, tp12034, tm12034, ep12034, em12034, dsL]
  · norm_num [world12034, agent12034, scalar12034, tp12034, tm12034, ep12034, em12034, dsL]
  · norm_num [world12034, agent12034, scalar12034, tp12034, tm12034, ep12034, em12034, dsL]
  · norm_num [world12034, agent12034, scalar12034, tp12034, tm12034, ep12034, em12034, dsL]
  · norm_num [world12034, agent12034, scalar12034, tp12034, tm12034, ep12034, em12034, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12034, agent12034, tp12034, tm12034, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12034, agent12034, scalar12034, tp12034, tm12034, ep12034, em12034, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12034, agent12034, tp12034, tm12034, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12034, agent12034, scalar12034, tp12034, tm12034, ep12034, em12034, dsL]

theorem negative12034 :
    Eminus aL (agent12034.root+dsL) scalar12034.worldRadius world12034.frame
      agent12034.frame tm12034 ≤ -em12034 := by
  apply negative_check (lo := (16953651145341891703 / 25000000000000000000)) (hi := (67814604581367566813 / 100000000000000000000))
    (y := (-((73347684806865449767 / 100000000000000000000)))) (u := (9604727502954051759 / 20000000000000000000))
  · norm_num [world12034, agent12034, scalar12034, tp12034, tm12034, ep12034, em12034, dsL]
  · norm_num [world12034, agent12034, scalar12034, tp12034, tm12034, ep12034, em12034, dsL]
  · norm_num [world12034, agent12034, scalar12034, tp12034, tm12034, ep12034, em12034, dsL]
  · norm_num [world12034, agent12034, scalar12034, tp12034, tm12034, ep12034, em12034, dsL]
  · norm_num [world12034, agent12034, scalar12034, tp12034, tm12034, ep12034, em12034, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12034, agent12034, tp12034, tm12034, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12034, agent12034, tp12034, tm12034, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12034, agent12034, scalar12034, tp12034, tm12034, ep12034, em12034, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12034, agent12034, tp12034, tm12034, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12034, agent12034, scalar12034, tp12034, tm12034, ep12034, em12034, dsL]

theorem tails12034 :
    exp (-((12034:ℝ)*ep12034)) ≤ scalar12034.upperTail ∧
    exp (-((12034:ℝ)*em12034)) ≤ scalar12034.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12034:ℝ)) (by norm_num [ep12034]) ?_)
      (show bp12034^8 ≤ scalar12034.upperTail by norm_num [bp12034, scalar12034])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12034, bp12034, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12034:ℝ)) (by norm_num [em12034]) ?_)
      (show bm12034^8 ≤ scalar12034.lowerTail by norm_num [bm12034, scalar12034])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12034, bm12034, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12034 :
    agent12034.root+dsL+scalar12034.worldRadius < √(1/100/aL) ∧
    2*(agent12034.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12034, agent12034, scalar12034, tp12034, tm12034, ep12034, em12034, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12034, agent12034, scalar12034, tp12034, tm12034, ep12034, em12034, dsL]

noncomputable def master12034 : MasterCertificate 12034 world12034 agent12034 :=
  master scalar12034 dsL tp12034 tm12034 ep12034 em12034
    (by norm_num [dsL]) (by norm_num [tp12034]) (by norm_num [tm12034])
    (by norm_num [ep12034]) (by norm_num [em12034])
    positive12034 negative12034 tails12034.1 tails12034.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12034.1 tailGuards12034.2

theorem preserves12034 : master12034.toScalarCertificate = scalar12034 := rfl

noncomputable def tp12035 : ℝ := (1180694893 / 5000000000)
noncomputable def tm12035 : ℝ := (-((3056551651 / 5000000000)))
noncomputable def ep12035 : ℝ := (3391074807986567 / 6250000000000000000)
noncomputable def em12035 : ℝ := (52344562462802061 / 100000000000000000000)
noncomputable def bp12035 : ℝ := (44209446134734851819 / 100000000000000000000)
noncomputable def bm12035 : ℝ := (11374992588978431701 / 25000000000000000000)

theorem positive12035 :
    Eplus aL (agent12035.root+dsL) scalar12035.worldRadius world12035.frame
      agent12035.frame tp12035 ≤ -ep12035 := by
  apply positive_check (eT := (58093551384472083623 / 50000000000000000000)) (y := (2472044133877067401 / 6250000000000000000)) (u := (9282292242334020603 / 6250000000000000000))
  · norm_num [world12035, agent12035, scalar12035, tp12035, tm12035, ep12035, em12035, dsL]
  · norm_num [world12035, agent12035, scalar12035, tp12035, tm12035, ep12035, em12035, dsL]
  · norm_num [world12035, agent12035, scalar12035, tp12035, tm12035, ep12035, em12035, dsL]
  · norm_num [world12035, agent12035, scalar12035, tp12035, tm12035, ep12035, em12035, dsL]
  · norm_num [world12035, agent12035, scalar12035, tp12035, tm12035, ep12035, em12035, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12035, agent12035, tp12035, tm12035, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12035, agent12035, scalar12035, tp12035, tm12035, ep12035, em12035, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12035, agent12035, tp12035, tm12035, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12035, agent12035, scalar12035, tp12035, tm12035, ep12035, em12035, dsL]

theorem negative12035 :
    Eminus aL (agent12035.root+dsL) scalar12035.worldRadius world12035.frame
      agent12035.frame tm12035 ≤ -em12035 := by
  apply negative_check (lo := (67814239755849842289 / 100000000000000000000)) (hi := (6781423975584984229 / 10000000000000000000))
    (y := (-((3667366044867511251 / 5000000000000000000)))) (u := (48023812277674721311 / 100000000000000000000))
  · norm_num [world12035, agent12035, scalar12035, tp12035, tm12035, ep12035, em12035, dsL]
  · norm_num [world12035, agent12035, scalar12035, tp12035, tm12035, ep12035, em12035, dsL]
  · norm_num [world12035, agent12035, scalar12035, tp12035, tm12035, ep12035, em12035, dsL]
  · norm_num [world12035, agent12035, scalar12035, tp12035, tm12035, ep12035, em12035, dsL]
  · norm_num [world12035, agent12035, scalar12035, tp12035, tm12035, ep12035, em12035, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12035, agent12035, tp12035, tm12035, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12035, agent12035, tp12035, tm12035, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12035, agent12035, scalar12035, tp12035, tm12035, ep12035, em12035, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12035, agent12035, tp12035, tm12035, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12035, agent12035, scalar12035, tp12035, tm12035, ep12035, em12035, dsL]

theorem tails12035 :
    exp (-((12035:ℝ)*ep12035)) ≤ scalar12035.upperTail ∧
    exp (-((12035:ℝ)*em12035)) ≤ scalar12035.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12035:ℝ)) (by norm_num [ep12035]) ?_)
      (show bp12035^8 ≤ scalar12035.upperTail by norm_num [bp12035, scalar12035])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12035, bp12035, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12035:ℝ)) (by norm_num [em12035]) ?_)
      (show bm12035^8 ≤ scalar12035.lowerTail by norm_num [bm12035, scalar12035])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12035, bm12035, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12035 :
    agent12035.root+dsL+scalar12035.worldRadius < √(1/100/aL) ∧
    2*(agent12035.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12035, agent12035, scalar12035, tp12035, tm12035, ep12035, em12035, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12035, agent12035, scalar12035, tp12035, tm12035, ep12035, em12035, dsL]

noncomputable def master12035 : MasterCertificate 12035 world12035 agent12035 :=
  master scalar12035 dsL tp12035 tm12035 ep12035 em12035
    (by norm_num [dsL]) (by norm_num [tp12035]) (by norm_num [tm12035])
    (by norm_num [ep12035]) (by norm_num [em12035])
    positive12035 negative12035 tails12035.1 tails12035.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12035.1 tailGuards12035.2

theorem preserves12035 : master12035.toScalarCertificate = scalar12035 := rfl

noncomputable def tp12036 : ℝ := (2361493403 / 10000000000)
noncomputable def tm12036 : ℝ := (-((6113336403 / 10000000000)))
noncomputable def ep12036 : ℝ := (5426025683510459 / 10000000000000000000)
noncomputable def em12036 : ℝ := (52347230536352789 / 100000000000000000000)
noncomputable def bp12036 : ℝ := (44204412830925847667 / 100000000000000000000)
noncomputable def bm12036 : ℝ := (9099033418504695807 / 20000000000000000000)

theorem positive12036 :
    Eplus aL (agent12036.root+dsL) scalar12036.worldRadius world12036.frame
      agent12036.frame tp12036 ≤ -ep12036 := by
  apply positive_check (eT := (116187443613177260743 / 100000000000000000000)) (y := (39553374990181655803 / 100000000000000000000)) (u := (148517669231703276361 / 100000000000000000000))
  · norm_num [world12036, agent12036, scalar12036, tp12036, tm12036, ep12036, em12036, dsL]
  · norm_num [world12036, agent12036, scalar12036, tp12036, tm12036, ep12036, em12036, dsL]
  · norm_num [world12036, agent12036, scalar12036, tp12036, tm12036, ep12036, em12036, dsL]
  · norm_num [world12036, agent12036, scalar12036, tp12036, tm12036, ep12036, em12036, dsL]
  · norm_num [world12036, agent12036, scalar12036, tp12036, tm12036, ep12036, em12036, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12036, agent12036, tp12036, tm12036, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12036, agent12036, scalar12036, tp12036, tm12036, ep12036, em12036, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12036, agent12036, tp12036, tm12036, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12036, agent12036, scalar12036, tp12036, tm12036, ep12036, em12036, dsL]

theorem negative12036 :
    Eminus aL (agent12036.root+dsL) scalar12036.worldRadius world12036.frame
      agent12036.frame tm12036 ≤ -em12036 := by
  apply negative_check (lo := (4238367259439005577 / 6250000000000000000)) (hi := (67813876151024089233 / 100000000000000000000))
    (y := (-((73346955204629720569 / 100000000000000000000)))) (u := (24011993948790721951 / 50000000000000000000))
  · norm_num [world12036, agent12036, scalar12036, tp12036, tm12036, ep12036, em12036, dsL]
  · norm_num [world12036, agent12036, scalar12036, tp12036, tm12036, ep12036, em12036, dsL]
  · norm_num [world12036, agent12036, scalar12036, tp12036, tm12036, ep12036, em12036, dsL]
  · norm_num [world12036, agent12036, scalar12036, tp12036, tm12036, ep12036, em12036, dsL]
  · norm_num [world12036, agent12036, scalar12036, tp12036, tm12036, ep12036, em12036, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12036, agent12036, tp12036, tm12036, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12036, agent12036, tp12036, tm12036, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12036, agent12036, scalar12036, tp12036, tm12036, ep12036, em12036, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12036, agent12036, tp12036, tm12036, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12036, agent12036, scalar12036, tp12036, tm12036, ep12036, em12036, dsL]

theorem tails12036 :
    exp (-((12036:ℝ)*ep12036)) ≤ scalar12036.upperTail ∧
    exp (-((12036:ℝ)*em12036)) ≤ scalar12036.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12036:ℝ)) (by norm_num [ep12036]) ?_)
      (show bp12036^8 ≤ scalar12036.upperTail by norm_num [bp12036, scalar12036])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12036, bp12036, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12036:ℝ)) (by norm_num [em12036]) ?_)
      (show bm12036^8 ≤ scalar12036.lowerTail by norm_num [bm12036, scalar12036])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12036, bm12036, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12036 :
    agent12036.root+dsL+scalar12036.worldRadius < √(1/100/aL) ∧
    2*(agent12036.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12036, agent12036, scalar12036, tp12036, tm12036, ep12036, em12036, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12036, agent12036, scalar12036, tp12036, tm12036, ep12036, em12036, dsL]

noncomputable def master12036 : MasterCertificate 12036 world12036 agent12036 :=
  master scalar12036 dsL tp12036 tm12036 ep12036 em12036
    (by norm_num [dsL]) (by norm_num [tp12036]) (by norm_num [tm12036])
    (by norm_num [ep12036]) (by norm_num [em12036])
    positive12036 negative12036 tails12036.1 tails12036.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12036.1 tailGuards12036.2

theorem preserves12036 : master12036.toScalarCertificate = scalar12036 := rfl

noncomputable def tp12037 : ℝ := (590399243 / 2500000000)
noncomputable def tm12037 : ℝ := (-((6113569667 / 10000000000)))
noncomputable def ep12037 : ℝ := (1695728605556539 / 3125000000000000000)
noncomputable def em12037 : ℝ := (13087474324411383 / 25000000000000000000)
noncomputable def bp12037 : ℝ := (11049845167391663087 / 25000000000000000000)
noncomputable def bm12037 : ℝ := (355393476023079503 / 781250000000000000)

theorem positive12037 :
    Eplus aL (agent12037.root+dsL) scalar12037.worldRadius world12037.frame
      agent12037.frame tp12037 ≤ -ep12037 := by
  apply positive_check (eT := (4647511365580296667 / 4000000000000000000)) (y := (19777021846022530117 / 50000000000000000000)) (u := (37129665593861373811 / 25000000000000000000))
  · norm_num [world12037, agent12037, scalar12037, tp12037, tm12037, ep12037, em12037, dsL]
  · norm_num [world12037, agent12037, scalar12037, tp12037, tm12037, ep12037, em12037, dsL]
  · norm_num [world12037, agent12037, scalar12037, tp12037, tm12037, ep12037, em12037, dsL]
  · norm_num [world12037, agent12037, scalar12037, tp12037, tm12037, ep12037, em12037, dsL]
  · norm_num [world12037, agent12037, scalar12037, tp12037, tm12037, ep12037, em12037, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12037, agent12037, tp12037, tm12037, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12037, agent12037, scalar12037, tp12037, tm12037, ep12037, em12037, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12037, agent12037, tp12037, tm12037, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12037, agent12037, scalar12037, tp12037, tm12037, ep12037, em12037, dsL]

theorem negative12037 :
    Eminus aL (agent12037.root+dsL) scalar12037.worldRadius world12037.frame
      agent12037.frame tm12037 ≤ -em12037 := by
  apply negative_check (lo := (3390675589250476311 / 5000000000000000000)) (hi := (67813511785009526221 / 100000000000000000000))
    (y := (-((73346592419413032571 / 100000000000000000000)))) (u := (6003020265228253759 / 12500000000000000000))
  · norm_num [world12037, agent12037, scalar12037, tp12037, tm12037, ep12037, em12037, dsL]
  · norm_num [world12037, agent12037, scalar12037, tp12037, tm12037, ep12037, em12037, dsL]
  · norm_num [world12037, agent12037, scalar12037, tp12037, tm12037, ep12037, em12037, dsL]
  · norm_num [world12037, agent12037, scalar12037, tp12037, tm12037, ep12037, em12037, dsL]
  · norm_num [world12037, agent12037, scalar12037, tp12037, tm12037, ep12037, em12037, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12037, agent12037, tp12037, tm12037, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12037, agent12037, tp12037, tm12037, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12037, agent12037, scalar12037, tp12037, tm12037, ep12037, em12037, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12037, agent12037, tp12037, tm12037, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12037, agent12037, scalar12037, tp12037, tm12037, ep12037, em12037, dsL]

theorem tails12037 :
    exp (-((12037:ℝ)*ep12037)) ≤ scalar12037.upperTail ∧
    exp (-((12037:ℝ)*em12037)) ≤ scalar12037.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12037:ℝ)) (by norm_num [ep12037]) ?_)
      (show bp12037^8 ≤ scalar12037.upperTail by norm_num [bp12037, scalar12037])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12037, bp12037, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12037:ℝ)) (by norm_num [em12037]) ?_)
      (show bm12037^8 ≤ scalar12037.lowerTail by norm_num [bm12037, scalar12037])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12037, bm12037, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12037 :
    agent12037.root+dsL+scalar12037.worldRadius < √(1/100/aL) ∧
    2*(agent12037.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12037, agent12037, scalar12037, tp12037, tm12037, ep12037, em12037, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12037, agent12037, scalar12037, tp12037, tm12037, ep12037, em12037, dsL]

noncomputable def master12037 : MasterCertificate 12037 world12037 agent12037 :=
  master scalar12037 dsL tp12037 tm12037 ep12037 em12037
    (by norm_num [dsL]) (by norm_num [tp12037]) (by norm_num [tm12037])
    (by norm_num [ep12037]) (by norm_num [em12037])
    positive12037 negative12037 tails12037.1 tails12037.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12037.1 tailGuards12037.2

theorem preserves12037 : master12037.toScalarCertificate = scalar12037 := rfl

noncomputable def tp12038 : ℝ := (2361700487 / 10000000000)
noncomputable def tm12038 : ℝ := (-((764225319 / 1250000000)))
noncomputable def ep12038 : ℝ := (5426637219015109 / 10000000000000000000)
noncomputable def em12038 : ℝ := (52352562437826171 / 100000000000000000000)
noncomputable def bp12038 : ℝ := (11048587473462851581 / 25000000000000000000)
noncomputable def bm12038 : ℝ := (22742782041290571587 / 50000000000000000000)

theorem positive12038 :
    Eplus aL (agent12038.root+dsL) scalar12038.worldRadius world12038.frame
      agent12038.frame tp12038 ≤ -ep12038 := by
  apply positive_check (eT := (116188124303650736007 / 100000000000000000000)) (y := (19777356068880747593 / 50000000000000000000)) (u := (7425982757270015541 / 5000000000000000000))
  · norm_num [world12038, agent12038, scalar12038, tp12038, tm12038, ep12038, em12038, dsL]
  · norm_num [world12038, agent12038, scalar12038, tp12038, tm12038, ep12038, em12038, dsL]
  · norm_num [world12038, agent12038, scalar12038, tp12038, tm12038, ep12038, em12038, dsL]
  · norm_num [world12038, agent12038, scalar12038, tp12038, tm12038, ep12038, em12038, dsL]
  · norm_num [world12038, agent12038, scalar12038, tp12038, tm12038, ep12038, em12038, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12038, agent12038, tp12038, tm12038, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12038, agent12038, scalar12038, tp12038, tm12038, ep12038, em12038, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12038, agent12038, tp12038, tm12038, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12038, agent12038, scalar12038, tp12038, tm12038, ep12038, em12038, dsL]

theorem negative12038 :
    Eminus aL (agent12038.root+dsL) scalar12038.worldRadius world12038.frame
      agent12038.frame tm12038 ≤ -em12038 := by
  apply negative_check (lo := (8476643624118944829 / 12500000000000000000)) (hi := (67813148992951558633 / 100000000000000000000))
    (y := (-((14669245443125087239 / 20000000000000000000)))) (u := (2401216875410265953 / 5000000000000000000))
  · norm_num [world12038, agent12038, scalar12038, tp12038, tm12038, ep12038, em12038, dsL]
  · norm_num [world12038, agent12038, scalar12038, tp12038, tm12038, ep12038, em12038, dsL]
  · norm_num [world12038, agent12038, scalar12038, tp12038, tm12038, ep12038, em12038, dsL]
  · norm_num [world12038, agent12038, scalar12038, tp12038, tm12038, ep12038, em12038, dsL]
  · norm_num [world12038, agent12038, scalar12038, tp12038, tm12038, ep12038, em12038, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12038, agent12038, tp12038, tm12038, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12038, agent12038, tp12038, tm12038, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12038, agent12038, scalar12038, tp12038, tm12038, ep12038, em12038, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12038, agent12038, tp12038, tm12038, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12038, agent12038, scalar12038, tp12038, tm12038, ep12038, em12038, dsL]

theorem tails12038 :
    exp (-((12038:ℝ)*ep12038)) ≤ scalar12038.upperTail ∧
    exp (-((12038:ℝ)*em12038)) ≤ scalar12038.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12038:ℝ)) (by norm_num [ep12038]) ?_)
      (show bp12038^8 ≤ scalar12038.upperTail by norm_num [bp12038, scalar12038])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12038, bp12038, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12038:ℝ)) (by norm_num [em12038]) ?_)
      (show bm12038^8 ≤ scalar12038.lowerTail by norm_num [bm12038, scalar12038])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12038, bm12038, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12038 :
    agent12038.root+dsL+scalar12038.worldRadius < √(1/100/aL) ∧
    2*(agent12038.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12038, agent12038, scalar12038, tp12038, tm12038, ep12038, em12038, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12038, agent12038, scalar12038, tp12038, tm12038, ep12038, em12038, dsL]

noncomputable def master12038 : MasterCertificate 12038 world12038 agent12038 :=
  master scalar12038 dsL tp12038 tm12038 ep12038 em12038
    (by norm_num [dsL]) (by norm_num [tp12038]) (by norm_num [tm12038])
    (by norm_num [ep12038]) (by norm_num [em12038])
    positive12038 negative12038 tails12038.1 tails12038.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12038.1 tailGuards12038.2

theorem preserves12038 : master12038.toScalarCertificate = scalar12038 := rfl

noncomputable def tp12039 : ℝ := (2361803949 / 10000000000)
noncomputable def tm12039 : ℝ := (-((1528508831 / 2500000000)))
noncomputable def ep12039 : ℝ := (54269426410352571 / 100000000000000000000)
noncomputable def em12039 : ℝ := (10471045038609609 / 20000000000000000000)
noncomputable def bp12039 : ℝ := (11047330269200257979 / 25000000000000000000)
noncomputable def bm12039 : ℝ := (45480765070170623887 / 100000000000000000000)

theorem positive12039 :
    Eplus aL (agent12039.root+dsL) scalar12039.worldRadius world12039.frame
      agent12039.frame tp12039 ≤ -ep12039 := by
  apply positive_check (eT := (116188464113051454671 / 100000000000000000000)) (y := (7911076079085006467 / 20000000000000000000)) (u := (74260323821346947411 / 50000000000000000000))
  · norm_num [world12039, agent12039, scalar12039, tp12039, tm12039, ep12039, em12039, dsL]
  · norm_num [world12039, agent12039, scalar12039, tp12039, tm12039, ep12039, em12039, dsL]
  · norm_num [world12039, agent12039, scalar12039, tp12039, tm12039, ep12039, em12039, dsL]
  · norm_num [world12039, agent12039, scalar12039, tp12039, tm12039, ep12039, em12039, dsL]
  · norm_num [world12039, agent12039, scalar12039, tp12039, tm12039, ep12039, em12039, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12039, agent12039, tp12039, tm12039, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12039, agent12039, scalar12039, tp12039, tm12039, ep12039, em12039, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12039, agent12039, tp12039, tm12039, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12039, agent12039, scalar12039, tp12039, tm12039, ep12039, em12039, dsL]

theorem negative12039 :
    Eminus aL (agent12039.root+dsL) scalar12039.worldRadius world12039.frame
      agent12039.frame tm12039 ≤ -em12039 := by
  apply negative_check (lo := (2119149582146886713 / 3125000000000000000)) (hi := (67812786628700374817 / 100000000000000000000))
    (y := (-((573014547428948617 / 781250000000000000)))) (u := (9604902573371641567 / 20000000000000000000))
  · norm_num [world12039, agent12039, scalar12039, tp12039, tm12039, ep12039, em12039, dsL]
  · norm_num [world12039, agent12039, scalar12039, tp12039, tm12039, ep12039, em12039, dsL]
  · norm_num [world12039, agent12039, scalar12039, tp12039, tm12039, ep12039, em12039, dsL]
  · norm_num [world12039, agent12039, scalar12039, tp12039, tm12039, ep12039, em12039, dsL]
  · norm_num [world12039, agent12039, scalar12039, tp12039, tm12039, ep12039, em12039, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12039, agent12039, tp12039, tm12039, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12039, agent12039, tp12039, tm12039, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12039, agent12039, scalar12039, tp12039, tm12039, ep12039, em12039, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12039, agent12039, tp12039, tm12039, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12039, agent12039, scalar12039, tp12039, tm12039, ep12039, em12039, dsL]

theorem tails12039 :
    exp (-((12039:ℝ)*ep12039)) ≤ scalar12039.upperTail ∧
    exp (-((12039:ℝ)*em12039)) ≤ scalar12039.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12039:ℝ)) (by norm_num [ep12039]) ?_)
      (show bp12039^8 ≤ scalar12039.upperTail by norm_num [bp12039, scalar12039])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12039, bp12039, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12039:ℝ)) (by norm_num [em12039]) ?_)
      (show bm12039^8 ≤ scalar12039.lowerTail by norm_num [bm12039, scalar12039])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12039, bm12039, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12039 :
    agent12039.root+dsL+scalar12039.worldRadius < √(1/100/aL) ∧
    2*(agent12039.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12039, agent12039, scalar12039, tp12039, tm12039, ep12039, em12039, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12039, agent12039, scalar12039, tp12039, tm12039, ep12039, em12039, dsL]

noncomputable def master12039 : MasterCertificate 12039 world12039 agent12039 :=
  master scalar12039 dsL tp12039 tm12039 ep12039 em12039
    (by norm_num [dsL]) (by norm_num [tp12039]) (by norm_num [tm12039])
    (by norm_num [ep12039]) (by norm_num [em12039])
    positive12039 negative12039 tails12039.1 tails12039.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12039.1 tailGuards12039.2

theorem preserves12039 : master12039.toScalarCertificate = scalar12039 := rfl

noncomputable def tp12040 : ℝ := (118095367 / 500000000)
noncomputable def tm12040 : ℝ := (-((3057133997 / 5000000000)))
noncomputable def ep12040 : ℝ := (13568119817850287 / 25000000000000000000)
noncomputable def em12040 : ℝ := (3272367915054811 / 6250000000000000000)
noncomputable def bp12040 : ℝ := (44184293398402560633 / 100000000000000000000)
noncomputable def bm12040 : ℝ := (45475967156154724957 / 100000000000000000000)

theorem positive12040 :
    Eplus aL (agent12040.root+dsL) scalar12040.worldRadius world12040.frame
      agent12040.frame tp12040 ≤ -ep12040 := by
  apply positive_check (eT := (14523600429350086353 / 12500000000000000000)) (y := (791120961816255533 / 2000000000000000000)) (u := (74260819655759356447 / 50000000000000000000))
  · norm_num [world12040, agent12040, scalar12040, tp12040, tm12040, ep12040, em12040, dsL]
  · norm_num [world12040, agent12040, scalar12040, tp12040, tm12040, ep12040, em12040, dsL]
  · norm_num [world12040, agent12040, scalar12040, tp12040, tm12040, ep12040, em12040, dsL]
  · norm_num [world12040, agent12040, scalar12040, tp12040, tm12040, ep12040, em12040, dsL]
  · norm_num [world12040, agent12040, scalar12040, tp12040, tm12040, ep12040, em12040, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12040, agent12040, tp12040, tm12040, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12040, agent12040, scalar12040, tp12040, tm12040, ep12040, em12040, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12040, agent12040, tp12040, tm12040, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12040, agent12040, scalar12040, tp12040, tm12040, ep12040, em12040, dsL]

theorem negative12040 :
    Eminus aL (agent12040.root+dsL) scalar12040.worldRadius world12040.frame
      agent12040.frame tm12040 ≤ -em12040 := by
  apply negative_check (lo := (67812424644937914357 / 100000000000000000000)) (hi := (33906212322468957179 / 50000000000000000000))
    (y := (-((3667274861481262651 / 5000000000000000000)))) (u := (24012344040212686091 / 50000000000000000000))
  · norm_num [world12040, agent12040, scalar12040, tp12040, tm12040, ep12040, em12040, dsL]
  · norm_num [world12040, agent12040, scalar12040, tp12040, tm12040, ep12040, em12040, dsL]
  · norm_num [world12040, agent12040, scalar12040, tp12040, tm12040, ep12040, em12040, dsL]
  · norm_num [world12040, agent12040, scalar12040, tp12040, tm12040, ep12040, em12040, dsL]
  · norm_num [world12040, agent12040, scalar12040, tp12040, tm12040, ep12040, em12040, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12040, agent12040, tp12040, tm12040, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12040, agent12040, tp12040, tm12040, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12040, agent12040, scalar12040, tp12040, tm12040, ep12040, em12040, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12040, agent12040, tp12040, tm12040, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12040, agent12040, scalar12040, tp12040, tm12040, ep12040, em12040, dsL]

theorem tails12040 :
    exp (-((12040:ℝ)*ep12040)) ≤ scalar12040.upperTail ∧
    exp (-((12040:ℝ)*em12040)) ≤ scalar12040.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12040:ℝ)) (by norm_num [ep12040]) ?_)
      (show bp12040^8 ≤ scalar12040.upperTail by norm_num [bp12040, scalar12040])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12040, bp12040, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12040:ℝ)) (by norm_num [em12040]) ?_)
      (show bm12040^8 ≤ scalar12040.lowerTail by norm_num [bm12040, scalar12040])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12040, bm12040, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12040 :
    agent12040.root+dsL+scalar12040.worldRadius < √(1/100/aL) ∧
    2*(agent12040.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12040, agent12040, scalar12040, tp12040, tm12040, ep12040, em12040, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12040, agent12040, scalar12040, tp12040, tm12040, ep12040, em12040, dsL]

noncomputable def master12040 : MasterCertificate 12040 world12040 agent12040 :=
  master scalar12040 dsL tp12040 tm12040 ep12040 em12040
    (by norm_num [dsL]) (by norm_num [tp12040]) (by norm_num [tm12040])
    (by norm_num [ep12040]) (by norm_num [em12040])
    positive12040 negative12040 tails12040.1 tails12040.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12040.1 tailGuards12040.2

theorem preserves12040 : master12040.toScalarCertificate = scalar12040 := rfl

noncomputable def tp12041 : ℝ := (1181005361 / 5000000000)
noncomputable def tm12041 : ℝ := (-((764312583 / 1250000000)))
noncomputable def ep12041 : ℝ := (54275531146397289 / 100000000000000000000)
noncomputable def em12041 : ℝ := (10472109439529881 / 20000000000000000000)
noncomputable def bp12041 : ℝ := (44179266610528370151 / 100000000000000000000)
noncomputable def bm12041 : ℝ := (22735585027787886859 / 50000000000000000000)

theorem positive12041 :
    Eplus aL (agent12041.root+dsL) scalar12041.worldRadius world12041.frame
      agent12041.frame tp12041 ≤ -ep12041 := by
  apply positive_check (eT := (58094571363310568793 / 50000000000000000000)) (y := (19778358037942958319 / 50000000000000000000)) (u := (148522631417213251937 / 100000000000000000000))
  · norm_num [world12041, agent12041, scalar12041, tp12041, tm12041, ep12041, em12041, dsL]
  · norm_num [world12041, agent12041, scalar12041, tp12041, tm12041, ep12041, em12041, dsL]
  · norm_num [world12041, agent12041, scalar12041, tp12041, tm12041, ep12041, em12041, dsL]
  · norm_num [world12041, agent12041, scalar12041, tp12041, tm12041, ep12041, em12041, dsL]
  · norm_num [world12041, agent12041, scalar12041, tp12041, tm12041, ep12041, em12041, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12041, agent12041, tp12041, tm12041, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12041, agent12041, scalar12041, tp12041, tm12041, ep12041, em12041, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12041, agent12041, tp12041, tm12041, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12041, agent12041, scalar12041, tp12041, tm12041, ep12041, em12041, dsL]

theorem negative12041 :
    Eminus aL (agent12041.root+dsL) scalar12041.worldRadius world12041.frame
      agent12041.frame tm12041 ≤ -em12041 := by
  apply negative_check (lo := (271248250408526719 / 400000000000000000)) (hi := (67812062602131679751 / 100000000000000000000))
    (y := (-((1146017713222228179 / 1562500000000000000)))) (u := (24012431345268916667 / 50000000000000000000))
  · norm_num [world12041, agent12041, scalar12041, tp12041, tm12041, ep12041, em12041, dsL]
  · norm_num [world12041, agent12041, scalar12041, tp12041, tm12041, ep12041, em12041, dsL]
  · norm_num [world12041, agent12041, scalar12041, tp12041, tm12041, ep12041, em12041, dsL]
  · norm_num [world12041, agent12041, scalar12041, tp12041, tm12041, ep12041, em12041, dsL]
  · norm_num [world12041, agent12041, scalar12041, tp12041, tm12041, ep12041, em12041, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12041, agent12041, tp12041, tm12041, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12041, agent12041, tp12041, tm12041, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12041, agent12041, scalar12041, tp12041, tm12041, ep12041, em12041, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12041, agent12041, tp12041, tm12041, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12041, agent12041, scalar12041, tp12041, tm12041, ep12041, em12041, dsL]

theorem tails12041 :
    exp (-((12041:ℝ)*ep12041)) ≤ scalar12041.upperTail ∧
    exp (-((12041:ℝ)*em12041)) ≤ scalar12041.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12041:ℝ)) (by norm_num [ep12041]) ?_)
      (show bp12041^8 ≤ scalar12041.upperTail by norm_num [bp12041, scalar12041])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12041, bp12041, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12041:ℝ)) (by norm_num [em12041]) ?_)
      (show bm12041^8 ≤ scalar12041.lowerTail by norm_num [bm12041, scalar12041])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12041, bm12041, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12041 :
    agent12041.root+dsL+scalar12041.worldRadius < √(1/100/aL) ∧
    2*(agent12041.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12041, agent12041, scalar12041, tp12041, tm12041, ep12041, em12041, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12041, agent12041, scalar12041, tp12041, tm12041, ep12041, em12041, dsL]

noncomputable def master12041 : MasterCertificate 12041 world12041 agent12041 :=
  master scalar12041 dsL tp12041 tm12041 ep12041 em12041
    (by norm_num [dsL]) (by norm_num [tp12041]) (by norm_num [tm12041])
    (by norm_num [ep12041]) (by norm_num [em12041])
    positive12041 negative12041 tails12041.1 tails12041.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12041.1 tailGuards12041.2

theorem preserves12041 : master12041.toScalarCertificate = scalar12041 := rfl

noncomputable def tp12042 : ℝ := (2362113987 / 10000000000)
noncomputable def tm12042 : ℝ := (-((6114732919 / 10000000000)))
noncomputable def ep12042 : ℝ := (54278580543497881 / 100000000000000000000)
noncomputable def em12042 : ℝ := (52363205401152599 / 100000000000000000000)
noncomputable def bp12042 : ℝ := (44174241705143383119 / 100000000000000000000)
noncomputable def bm12042 : ℝ := (45466374769148004563 / 100000000000000000000)

theorem positive12042 :
    Eplus aL (agent12042.root+dsL) scalar12042.worldRadius world12042.frame
      agent12042.frame tp12042 ≤ -ep12042 := by
  apply positive_check (eT := (116189481191309556583 / 100000000000000000000)) (y := (19778691465781511819 / 50000000000000000000)) (u := (148523621852115028343 / 100000000000000000000))
  · norm_num [world12042, agent12042, scalar12042, tp12042, tm12042, ep12042, em12042, dsL]
  · norm_num [world12042, agent12042, scalar12042, tp12042, tm12042, ep12042, em12042, dsL]
  · norm_num [world12042, agent12042, scalar12042, tp12042, tm12042, ep12042, em12042, dsL]
  · norm_num [world12042, agent12042, scalar12042, tp12042, tm12042, ep12042, em12042, dsL]
  · norm_num [world12042, agent12042, scalar12042, tp12042, tm12042, ep12042, em12042, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12042, agent12042, tp12042, tm12042, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12042, agent12042, scalar12042, tp12042, tm12042, ep12042, em12042, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12042, agent12042, tp12042, tm12042, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12042, agent12042, scalar12042, tp12042, tm12042, ep12042, em12042, dsL]

theorem negative12042 :
    Eminus aL (agent12042.root+dsL) scalar12042.worldRadius world12042.frame
      agent12042.frame tm12042 ≤ -em12042 := by
  apply negative_check (lo := (3390585114404604769 / 5000000000000000000)) (hi := (67811702288092095381 / 100000000000000000000))
    (y := (-((18336191832545907469 / 25000000000000000000)))) (u := (48025038613634780877 / 100000000000000000000))
  · norm_num [world12042, agent12042, scalar12042, tp12042, tm12042, ep12042, em12042, dsL]
  · norm_num [world12042, agent12042, scalar12042, tp12042, tm12042, ep12042, em12042, dsL]
  · norm_num [world12042, agent12042, scalar12042, tp12042, tm12042, ep12042, em12042, dsL]
  · norm_num [world12042, agent12042, scalar12042, tp12042, tm12042, ep12042, em12042, dsL]
  · norm_num [world12042, agent12042, scalar12042, tp12042, tm12042, ep12042, em12042, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12042, agent12042, tp12042, tm12042, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12042, agent12042, tp12042, tm12042, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12042, agent12042, scalar12042, tp12042, tm12042, ep12042, em12042, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12042, agent12042, tp12042, tm12042, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12042, agent12042, scalar12042, tp12042, tm12042, ep12042, em12042, dsL]

theorem tails12042 :
    exp (-((12042:ℝ)*ep12042)) ≤ scalar12042.upperTail ∧
    exp (-((12042:ℝ)*em12042)) ≤ scalar12042.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12042:ℝ)) (by norm_num [ep12042]) ?_)
      (show bp12042^8 ≤ scalar12042.upperTail by norm_num [bp12042, scalar12042])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12042, bp12042, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12042:ℝ)) (by norm_num [em12042]) ?_)
      (show bm12042^8 ≤ scalar12042.lowerTail by norm_num [bm12042, scalar12042])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12042, bm12042, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12042 :
    agent12042.root+dsL+scalar12042.worldRadius < √(1/100/aL) ∧
    2*(agent12042.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12042, agent12042, scalar12042, tp12042, tm12042, ep12042, em12042, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12042, agent12042, scalar12042, tp12042, tm12042, ep12042, em12042, dsL]

noncomputable def master12042 : MasterCertificate 12042 world12042 agent12042 :=
  master scalar12042 dsL tp12042 tm12042 ep12042 em12042
    (by norm_num [dsL]) (by norm_num [tp12042]) (by norm_num [tm12042])
    (by norm_num [ep12042]) (by norm_num [em12042])
    positive12042 negative12042 tails12042.1 tails12042.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12042.1 tailGuards12042.2

theorem preserves12042 : master12042.toScalarCertificate = scalar12042 := rfl

noncomputable def tp12043 : ℝ := (1181108619 / 5000000000)
noncomputable def tm12043 : ℝ := (-((122299307 / 200000000)))
noncomputable def ep12043 : ℝ := (54281628844277283 / 100000000000000000000)
noncomputable def em12043 : ℝ := (52365862584620813 / 100000000000000000000)
noncomputable def bp12043 : ℝ := (1380288055109996353 / 3125000000000000000)
noncomputable def bm12043 : ℝ := (4546158038438348027 / 10000000000000000000)

theorem positive12043 :
    Eplus aL (agent12043.root+dsL) scalar12043.worldRadius world12043.frame
      agent12043.frame tp12043 ≤ -ep12043 := by
  apply positive_check (eT := (58094909794572771681 / 50000000000000000000)) (y := (39558050038887539263 / 100000000000000000000)) (u := (148524612667379936619 / 100000000000000000000))
  · norm_num [world12043, agent12043, scalar12043, tp12043, tm12043, ep12043, em12043, dsL]
  · norm_num [world12043, agent12043, scalar12043, tp12043, tm12043, ep12043, em12043, dsL]
  · norm_num [world12043, agent12043, scalar12043, tp12043, tm12043, ep12043, em12043, dsL]
  · norm_num [world12043, agent12043, scalar12043, tp12043, tm12043, ep12043, em12043, dsL]
  · norm_num [world12043, agent12043, scalar12043, tp12043, tm12043, ep12043, em12043, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12043, agent12043, tp12043, tm12043, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12043, agent12043, scalar12043, tp12043, tm12043, ep12043, em12043, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12043, agent12043, tp12043, tm12043, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12043, agent12043, scalar12043, tp12043, tm12043, ep12043, em12043, dsL]

theorem negative12043 :
    Eminus aL (agent12043.root+dsL) scalar12043.worldRadius world12043.frame
      agent12043.frame tm12043 ≤ -em12043 := by
  apply negative_check (lo := (67811341156870458623 / 100000000000000000000)) (hi := (264888051394025229 / 390625000000000000))
    (y := (-((7334440387270036379 / 10000000000000000000)))) (u := (48025213164548672547 / 100000000000000000000))
  · norm_num [world12043, agent12043, scalar12043, tp12043, tm12043, ep12043, em12043, dsL]
  · norm_num [world12043, agent12043, scalar12043, tp12043, tm12043, ep12043, em12043, dsL]
  · norm_num [world12043, agent12043, scalar12043, tp12043, tm12043, ep12043, em12043, dsL]
  · norm_num [world12043, agent12043, scalar12043, tp12043, tm12043, ep12043, em12043, dsL]
  · norm_num [world12043, agent12043, scalar12043, tp12043, tm12043, ep12043, em12043, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12043, agent12043, tp12043, tm12043, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12043, agent12043, tp12043, tm12043, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12043, agent12043, scalar12043, tp12043, tm12043, ep12043, em12043, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12043, agent12043, tp12043, tm12043, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12043, agent12043, scalar12043, tp12043, tm12043, ep12043, em12043, dsL]

theorem tails12043 :
    exp (-((12043:ℝ)*ep12043)) ≤ scalar12043.upperTail ∧
    exp (-((12043:ℝ)*em12043)) ≤ scalar12043.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12043:ℝ)) (by norm_num [ep12043]) ?_)
      (show bp12043^8 ≤ scalar12043.upperTail by norm_num [bp12043, scalar12043])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12043, bp12043, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12043:ℝ)) (by norm_num [em12043]) ?_)
      (show bm12043^8 ≤ scalar12043.lowerTail by norm_num [bm12043, scalar12043])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12043, bm12043, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12043 :
    agent12043.root+dsL+scalar12043.worldRadius < √(1/100/aL) ∧
    2*(agent12043.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12043, agent12043, scalar12043, tp12043, tm12043, ep12043, em12043, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12043, agent12043, scalar12043, tp12043, tm12043, ep12043, em12043, dsL]

noncomputable def master12043 : MasterCertificate 12043 world12043 agent12043 :=
  master scalar12043 dsL tp12043 tm12043 ep12043 em12043
    (by norm_num [dsL]) (by norm_num [tp12043]) (by norm_num [tm12043])
    (by norm_num [ep12043]) (by norm_num [em12043])
    positive12043 negative12043 tails12043.1 tails12043.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12043.1 tailGuards12043.2

theorem preserves12043 : master12043.toScalarCertificate = scalar12043 := rfl

noncomputable def tp12044 : ℝ := (2362320413 / 10000000000)
noncomputable def tm12044 : ℝ := (-((6115197413 / 10000000000)))
noncomputable def ep12044 : ℝ := (10856934912689569 / 20000000000000000000)
noncomputable def em12044 : ℝ := (6392641283259 / 12207031250000000)
noncomputable def bp12044 : ℝ := (2760262235824776501 / 6250000000000000000)
noncomputable def bm12044 : ℝ := (22728393914491224783 / 50000000000000000000)

theorem positive12044 :
    Eplus aL (agent12044.root+dsL) scalar12044.worldRadius world12044.frame
      agent12044.frame tp12044 ≤ -ep12044 := by
  apply positive_check (eT := (116190157462523136489 / 100000000000000000000)) (y := (19779358270709388359 / 50000000000000000000)) (u := (742628012954909023 / 500000000000000000))
  · norm_num [world12044, agent12044, scalar12044, tp12044, tm12044, ep12044, em12044, dsL]
  · norm_num [world12044, agent12044, scalar12044, tp12044, tm12044, ep12044, em12044, dsL]
  · norm_num [world12044, agent12044, scalar12044, tp12044, tm12044, ep12044, em12044, dsL]
  · norm_num [world12044, agent12044, scalar12044, tp12044, tm12044, ep12044, em12044, dsL]
  · norm_num [world12044, agent12044, scalar12044, tp12044, tm12044, ep12044, em12044, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12044, agent12044, tp12044, tm12044, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12044, agent12044, scalar12044, tp12044, tm12044, ep12044, em12044, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12044, agent12044, tp12044, tm12044, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12044, agent12044, scalar12044, tp12044, tm12044, ep12044, em12044, dsL]

theorem negative12044 :
    Eminus aL (agent12044.root+dsL) scalar12044.worldRadius world12044.frame
      agent12044.frame tm12044 ≤ -em12044 := by
  apply negative_check (lo := (2712439262072673031 / 4000000000000000000)) (hi := (4238186346988551611 / 6250000000000000000))
    (y := (-((14668807593512606991 / 20000000000000000000)))) (u := (48025388891592351699 / 100000000000000000000))
  · norm_num [world12044, agent12044, scalar12044, tp12044, tm12044, ep12044, em12044, dsL]
  · norm_num [world12044, agent12044, scalar12044, tp12044, tm12044, ep12044, em12044, dsL]
  · norm_num [world12044, agent12044, scalar12044, tp12044, tm12044, ep12044, em12044, dsL]
  · norm_num [world12044, agent12044, scalar12044, tp12044, tm12044, ep12044, em12044, dsL]
  · norm_num [world12044, agent12044, scalar12044, tp12044, tm12044, ep12044, em12044, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12044, agent12044, tp12044, tm12044, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12044, agent12044, tp12044, tm12044, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12044, agent12044, scalar12044, tp12044, tm12044, ep12044, em12044, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12044, agent12044, tp12044, tm12044, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12044, agent12044, scalar12044, tp12044, tm12044, ep12044, em12044, dsL]

theorem tails12044 :
    exp (-((12044:ℝ)*ep12044)) ≤ scalar12044.upperTail ∧
    exp (-((12044:ℝ)*em12044)) ≤ scalar12044.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12044:ℝ)) (by norm_num [ep12044]) ?_)
      (show bp12044^8 ≤ scalar12044.upperTail by norm_num [bp12044, scalar12044])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12044, bp12044, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12044:ℝ)) (by norm_num [em12044]) ?_)
      (show bm12044^8 ≤ scalar12044.lowerTail by norm_num [bm12044, scalar12044])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12044, bm12044, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12044 :
    agent12044.root+dsL+scalar12044.worldRadius < √(1/100/aL) ∧
    2*(agent12044.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12044, agent12044, scalar12044, tp12044, tm12044, ep12044, em12044, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12044, agent12044, scalar12044, tp12044, tm12044, ep12044, em12044, dsL]

noncomputable def master12044 : MasterCertificate 12044 world12044 agent12044 :=
  master scalar12044 dsL tp12044 tm12044 ep12044 em12044
    (by norm_num [dsL]) (by norm_num [tp12044]) (by norm_num [tm12044])
    (by norm_num [ep12044]) (by norm_num [em12044])
    positive12044 negative12044 tails12044.1 tails12044.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12044.1 tailGuards12044.2

theorem preserves12044 : master12044.toScalarCertificate = scalar12044 := rfl

noncomputable def tp12045 : ℝ := (2362423567 / 10000000000)
noncomputable def tm12045 : ℝ := (-((611542941 / 1000000000)))
noncomputable def ep12045 : ℝ := (54287719411239161 / 100000000000000000000)
noncomputable def em12045 : ℝ := (26185585670696641 / 50000000000000000000)
noncomputable def bp12045 : ℝ := (22079587298490893439 / 50000000000000000000)
noncomputable def bm12045 : ℝ := (1818079842596960257 / 4000000000000000000)

theorem positive12045 :
    Eplus aL (agent12045.root+dsL) scalar12045.worldRadius world12045.frame
      agent12045.frame tp12045 ≤ -ep12045 := by
  apply positive_check (eT := (58095247608705240951 / 50000000000000000000)) (y := (39559383329649100563 / 100000000000000000000)) (u := (148526592945520678917 / 100000000000000000000))
  · norm_num [world12045, agent12045, scalar12045, tp12045, tm12045, ep12045, em12045, dsL]
  · norm_num [world12045, agent12045, scalar12045, tp12045, tm12045, ep12045, em12045, dsL]
  · norm_num [world12045, agent12045, scalar12045, tp12045, tm12045, ep12045, em12045, dsL]
  · norm_num [world12045, agent12045, scalar12045, tp12045, tm12045, ep12045, em12045, dsL]
  · norm_num [world12045, agent12045, scalar12045, tp12045, tm12045, ep12045, em12045, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12045, agent12045, tp12045, tm12045, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12045, agent12045, scalar12045, tp12045, tm12045, ep12045, em12045, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12045, agent12045, tp12045, tm12045, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12045, agent12045, scalar12045, tp12045, tm12045, ep12045, em12045, dsL]

theorem negative12045 :
    Eminus aL (agent12045.root+dsL) scalar12045.worldRadius world12045.frame
      agent12045.frame tm12045 ≤ -em12045 := by
  apply negative_check (lo := (67810622171967514781 / 100000000000000000000)) (hi := (33905311085983757391 / 50000000000000000000))
    (y := (-((9167959105551206209 / 12500000000000000000)))) (u := (48025564243726823653 / 100000000000000000000))
  · norm_num [world12045, agent12045, scalar12045, tp12045, tm12045, ep12045, em12045, dsL]
  · norm_num [world12045, agent12045, scalar12045, tp12045, tm12045, ep12045, em12045, dsL]
  · norm_num [world12045, agent12045, scalar12045, tp12045, tm12045, ep12045, em12045, dsL]
  · norm_num [world12045, agent12045, scalar12045, tp12045, tm12045, ep12045, em12045, dsL]
  · norm_num [world12045, agent12045, scalar12045, tp12045, tm12045, ep12045, em12045, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12045, agent12045, tp12045, tm12045, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12045, agent12045, tp12045, tm12045, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12045, agent12045, scalar12045, tp12045, tm12045, ep12045, em12045, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12045, agent12045, tp12045, tm12045, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12045, agent12045, scalar12045, tp12045, tm12045, ep12045, em12045, dsL]

theorem tails12045 :
    exp (-((12045:ℝ)*ep12045)) ≤ scalar12045.upperTail ∧
    exp (-((12045:ℝ)*em12045)) ≤ scalar12045.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12045:ℝ)) (by norm_num [ep12045]) ?_)
      (show bp12045^8 ≤ scalar12045.upperTail by norm_num [bp12045, scalar12045])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12045, bp12045, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12045:ℝ)) (by norm_num [em12045]) ?_)
      (show bm12045^8 ≤ scalar12045.lowerTail by norm_num [bm12045, scalar12045])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12045, bm12045, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12045 :
    agent12045.root+dsL+scalar12045.worldRadius < √(1/100/aL) ∧
    2*(agent12045.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12045, agent12045, scalar12045, tp12045, tm12045, ep12045, em12045, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12045, agent12045, scalar12045, tp12045, tm12045, ep12045, em12045, dsL]

noncomputable def master12045 : MasterCertificate 12045 world12045 agent12045 :=
  master scalar12045 dsL tp12045 tm12045 ep12045 em12045
    (by norm_num [dsL]) (by norm_num [tp12045]) (by norm_num [tm12045])
    (by norm_num [ep12045]) (by norm_num [em12045])
    positive12045 negative12045 tails12045.1 tails12045.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12045.1 tailGuards12045.2

theorem preserves12045 : master12045.toScalarCertificate = scalar12045 := rfl

noncomputable def tp12046 : ℝ := (2362526671 / 10000000000)
noncomputable def tm12046 : ℝ := (-((611566129 / 1000000000)))
noncomputable def ep12046 : ℝ := (13572690456070081 / 25000000000000000000)
noncomputable def em12046 : ℝ := (5237382306797433 / 10000000000000000000)
noncomputable def bp12046 : ℝ := (44154155274281410777 / 100000000000000000000)
noncomputable def bm12046 : ℝ := (45447206025250814761 / 100000000000000000000)

theorem positive12046 :
    Eplus aL (agent12046.root+dsL) scalar12046.worldRadius world12046.frame
      agent12046.frame tp12046 ≤ -ep12046 := by
  apply positive_check (eT := (11619083263977268429 / 10000000000000000000)) (y := (395600498212471767 / 1000000000000000000)) (u := (74263791433041217289 / 50000000000000000000))
  · norm_num [world12046, agent12046, scalar12046, tp12046, tm12046, ep12046, em12046, dsL]
  · norm_num [world12046, agent12046, scalar12046, tp12046, tm12046, ep12046, em12046, dsL]
  · norm_num [world12046, agent12046, scalar12046, tp12046, tm12046, ep12046, em12046, dsL]
  · norm_num [world12046, agent12046, scalar12046, tp12046, tm12046, ep12046, em12046, dsL]
  · norm_num [world12046, agent12046, scalar12046, tp12046, tm12046, ep12046, em12046, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12046, agent12046, tp12046, tm12046, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12046, agent12046, scalar12046, tp12046, tm12046, ep12046, em12046, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12046, agent12046, tp12046, tm12046, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12046, agent12046, scalar12046, tp12046, tm12046, ep12046, em12046, dsL]

theorem negative12046 :
    Eminus aL (agent12046.root+dsL) scalar12046.worldRadius world12046.frame
      agent12046.frame tm12046 ≤ -em12046 := by
  apply negative_check (lo := (678102632369941959 / 1000000000000000000)) (hi := (67810263236994195901 / 100000000000000000000))
    (y := (-((36671653719595401439 / 50000000000000000000)))) (u := (24012869865982786123 / 50000000000000000000))
  · norm_num [world12046, agent12046, scalar12046, tp12046, tm12046, ep12046, em12046, dsL]
  · norm_num [world12046, agent12046, scalar12046, tp12046, tm12046, ep12046, em12046, dsL]
  · norm_num [world12046, agent12046, scalar12046, tp12046, tm12046, ep12046, em12046, dsL]
  · norm_num [world12046, agent12046, scalar12046, tp12046, tm12046, ep12046, em12046, dsL]
  · norm_num [world12046, agent12046, scalar12046, tp12046, tm12046, ep12046, em12046, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12046, agent12046, tp12046, tm12046, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12046, agent12046, tp12046, tm12046, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12046, agent12046, scalar12046, tp12046, tm12046, ep12046, em12046, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12046, agent12046, tp12046, tm12046, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12046, agent12046, scalar12046, tp12046, tm12046, ep12046, em12046, dsL]

theorem tails12046 :
    exp (-((12046:ℝ)*ep12046)) ≤ scalar12046.upperTail ∧
    exp (-((12046:ℝ)*em12046)) ≤ scalar12046.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12046:ℝ)) (by norm_num [ep12046]) ?_)
      (show bp12046^8 ≤ scalar12046.upperTail by norm_num [bp12046, scalar12046])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12046, bp12046, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12046:ℝ)) (by norm_num [em12046]) ?_)
      (show bm12046^8 ≤ scalar12046.lowerTail by norm_num [bm12046, scalar12046])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12046, bm12046, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12046 :
    agent12046.root+dsL+scalar12046.worldRadius < √(1/100/aL) ∧
    2*(agent12046.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12046, agent12046, scalar12046, tp12046, tm12046, ep12046, em12046, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12046, agent12046, scalar12046, tp12046, tm12046, ep12046, em12046, dsL]

noncomputable def master12046 : MasterCertificate 12046 world12046 agent12046 :=
  master scalar12046 dsL tp12046 tm12046 ep12046 em12046
    (by norm_num [dsL]) (by norm_num [tp12046]) (by norm_num [tm12046])
    (by norm_num [ep12046]) (by norm_num [em12046])
    positive12046 negative12046 tails12046.1 tails12046.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12046.1 tailGuards12046.2

theorem preserves12046 : master12046.toScalarCertificate = scalar12046 := rfl

noncomputable def tp12047 : ℝ := (1181314843 / 5000000000)
noncomputable def tm12047 : ℝ := (-((76448663 / 125000000)))
noncomputable def ep12047 : ℝ := (13573450841625421 / 25000000000000000000)
noncomputable def em12047 : ℝ := (52376473936306991 / 100000000000000000000)
noncomputable def bp12047 : ℝ := (137966052391396927 / 312500000000000000)
noncomputable def bm12047 : ℝ := (45442416776436850707 / 100000000000000000000)

theorem positive12047 :
    Eplus aL (agent12047.root+dsL) scalar12047.worldRadius world12047.frame
      agent12047.frame tp12047 ≤ -ep12047 := by
  apply positive_check (eT := (58095584720896121217 / 50000000000000000000)) (y := (19780357685751273313 / 50000000000000000000)) (u := (2970571427901581391 / 2000000000000000000))
  · norm_num [world12047, agent12047, scalar12047, tp12047, tm12047, ep12047, em12047, dsL]
  · norm_num [world12047, agent12047, scalar12047, tp12047, tm12047, ep12047, em12047, dsL]
  · norm_num [world12047, agent12047, scalar12047, tp12047, tm12047, ep12047, em12047, dsL]
  · norm_num [world12047, agent12047, scalar12047, tp12047, tm12047, ep12047, em12047, dsL]
  · norm_num [world12047, agent12047, scalar12047, tp12047, tm12047, ep12047, em12047, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12047, agent12047, tp12047, tm12047, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12047, agent12047, scalar12047, tp12047, tm12047, ep12047, em12047, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12047, agent12047, tp12047, tm12047, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12047, agent12047, scalar12047, tp12047, tm12047, ep12047, em12047, dsL]

theorem negative12047 :
    Eminus aL (agent12047.root+dsL) scalar12047.worldRadius world12047.frame
      agent12047.frame tm12047 ≤ -em12047 := by
  apply negative_check (lo := (33904952401436998027 / 50000000000000000000)) (hi := (13561980960574799211 / 20000000000000000000))
    (y := (-((14668588437250895497 / 20000000000000000000)))) (u := (24012957573855245313 / 50000000000000000000))
  · norm_num [world12047, agent12047, scalar12047, tp12047, tm12047, ep12047, em12047, dsL]
  · norm_num [world12047, agent12047, scalar12047, tp12047, tm12047, ep12047, em12047, dsL]
  · norm_num [world12047, agent12047, scalar12047, tp12047, tm12047, ep12047, em12047, dsL]
  · norm_num [world12047, agent12047, scalar12047, tp12047, tm12047, ep12047, em12047, dsL]
  · norm_num [world12047, agent12047, scalar12047, tp12047, tm12047, ep12047, em12047, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12047, agent12047, tp12047, tm12047, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12047, agent12047, tp12047, tm12047, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12047, agent12047, scalar12047, tp12047, tm12047, ep12047, em12047, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12047, agent12047, tp12047, tm12047, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12047, agent12047, scalar12047, tp12047, tm12047, ep12047, em12047, dsL]

theorem tails12047 :
    exp (-((12047:ℝ)*ep12047)) ≤ scalar12047.upperTail ∧
    exp (-((12047:ℝ)*em12047)) ≤ scalar12047.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12047:ℝ)) (by norm_num [ep12047]) ?_)
      (show bp12047^8 ≤ scalar12047.upperTail by norm_num [bp12047, scalar12047])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12047, bp12047, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12047:ℝ)) (by norm_num [em12047]) ?_)
      (show bm12047^8 ≤ scalar12047.lowerTail by norm_num [bm12047, scalar12047])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12047, bm12047, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12047 :
    agent12047.root+dsL+scalar12047.worldRadius < √(1/100/aL) ∧
    2*(agent12047.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12047, agent12047, scalar12047, tp12047, tm12047, ep12047, em12047, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12047, agent12047, scalar12047, tp12047, tm12047, ep12047, em12047, dsL]

noncomputable def master12047 : MasterCertificate 12047 world12047 agent12047 :=
  master scalar12047 dsL tp12047 tm12047 ep12047 em12047
    (by norm_num [dsL]) (by norm_num [tp12047]) (by norm_num [tm12047])
    (by norm_num [ep12047]) (by norm_num [em12047])
    positive12047 negative12047 tails12047.1 tails12047.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12047.1 tailGuards12047.2

theorem preserves12047 : master12047.toScalarCertificate = scalar12047 := rfl

noncomputable def tp12048 : ℝ := (2362732673 / 10000000000)
noncomputable def tm12048 : ℝ := (-((6116124657 / 10000000000)))
noncomputable def ep12048 : ℝ := (54296842552411687 / 100000000000000000000)
noncomputable def em12048 : ℝ := (52379122590602771 / 100000000000000000000)
noncomputable def bp12048 : ℝ := (11036030014361324909 / 25000000000000000000)
noncomputable def bm12048 : ℝ := (22718814623119081247 / 50000000000000000000)

theorem positive12048 :
    Eplus aL (agent12048.root+dsL) scalar12048.worldRadius world12048.frame
      agent12048.frame tp12048 ≤ -ep12048 := by
  apply positive_check (eT := (58095753036848491811 / 50000000000000000000)) (y := (9890345335513389003 / 25000000000000000000)) (u := (148529560554918148687 / 100000000000000000000))
  · norm_num [world12048, agent12048, scalar12048, tp12048, tm12048, ep12048, em12048, dsL]
  · norm_num [world12048, agent12048, scalar12048, tp12048, tm12048, ep12048, em12048, dsL]
  · norm_num [world12048, agent12048, scalar12048, tp12048, tm12048, ep12048, em12048, dsL]
  · norm_num [world12048, agent12048, scalar12048, tp12048, tm12048, ep12048, em12048, dsL]
  · norm_num [world12048, agent12048, scalar12048, tp12048, tm12048, ep12048, em12048, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12048, agent12048, tp12048, tm12048, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12048, agent12048, scalar12048, tp12048, tm12048, ep12048, em12048, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12048, agent12048, tp12048, tm12048, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12048, agent12048, scalar12048, tp12048, tm12048, ep12048, em12048, dsL]

theorem negative12048 :
    Eminus aL (agent12048.root+dsL) scalar12048.worldRadius world12048.frame
      agent12048.frame tm12048 ≤ -em12048 := by
  apply negative_check (lo := (13561909376493314437 / 20000000000000000000)) (hi := (33904773441233286093 / 50000000000000000000))
    (y := (-((36671288544708865171 / 50000000000000000000)))) (u := (48026090489127596573 / 100000000000000000000))
  · norm_num [world12048, agent12048, scalar12048, tp12048, tm12048, ep12048, em12048, dsL]
  · norm_num [world12048, agent12048, scalar12048, tp12048, tm12048, ep12048, em12048, dsL]
  · norm_num [world12048, agent12048, scalar12048, tp12048, tm12048, ep12048, em12048, dsL]
  · norm_num [world12048, agent12048, scalar12048, tp12048, tm12048, ep12048, em12048, dsL]
  · norm_num [world12048, agent12048, scalar12048, tp12048, tm12048, ep12048, em12048, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12048, agent12048, tp12048, tm12048, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12048, agent12048, tp12048, tm12048, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12048, agent12048, scalar12048, tp12048, tm12048, ep12048, em12048, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12048, agent12048, tp12048, tm12048, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12048, agent12048, scalar12048, tp12048, tm12048, ep12048, em12048, dsL]

theorem tails12048 :
    exp (-((12048:ℝ)*ep12048)) ≤ scalar12048.upperTail ∧
    exp (-((12048:ℝ)*em12048)) ≤ scalar12048.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12048:ℝ)) (by norm_num [ep12048]) ?_)
      (show bp12048^8 ≤ scalar12048.upperTail by norm_num [bp12048, scalar12048])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12048, bp12048, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12048:ℝ)) (by norm_num [em12048]) ?_)
      (show bm12048^8 ≤ scalar12048.lowerTail by norm_num [bm12048, scalar12048])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12048, bm12048, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12048 :
    agent12048.root+dsL+scalar12048.worldRadius < √(1/100/aL) ∧
    2*(agent12048.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12048, agent12048, scalar12048, tp12048, tm12048, ep12048, em12048, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12048, agent12048, scalar12048, tp12048, tm12048, ep12048, em12048, dsL]

noncomputable def master12048 : MasterCertificate 12048 world12048 agent12048 :=
  master scalar12048 dsL tp12048 tm12048 ep12048 em12048
    (by norm_num [dsL]) (by norm_num [tp12048]) (by norm_num [tm12048])
    (by norm_num [ep12048]) (by norm_num [em12048])
    positive12048 negative12048 tails12048.1 tails12048.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12048.1 tailGuards12048.2

theorem preserves12048 : master12048.toScalarCertificate = scalar12048 := rfl

noncomputable def tp12049 : ℝ := (2362835527 / 10000000000)
noncomputable def tm12049 : ℝ := (-((3058178051 / 5000000000)))
noncomputable def ep12049 : ℝ := (54299880428581297 / 100000000000000000000)
noncomputable def em12049 : ℝ := (6547721259276247 / 12500000000000000000)
noncomputable def bp12049 : ℝ := (5517388056878982391 / 12500000000000000000)
noncomputable def bm12049 : ℝ := (2271642136032875821 / 5000000000000000000)

theorem positive12049 :
    Eplus aL (agent12049.root+dsL) scalar12049.worldRadius world12049.frame
      agent12049.frame tp12049 ≤ -ep12049 := by
  apply positive_check (eT := (116191841760578690439 / 100000000000000000000)) (y := (1978102262745376353 / 5000000000000000000)) (u := (148530546665036071791 / 100000000000000000000))
  · norm_num [world12049, agent12049, scalar12049, tp12049, tm12049, ep12049, em12049, dsL]
  · norm_num [world12049, agent12049, scalar12049, tp12049, tm12049, ep12049, em12049, dsL]
  · norm_num [world12049, agent12049, scalar12049, tp12049, tm12049, ep12049, em12049, dsL]
  · norm_num [world12049, agent12049, scalar12049, tp12049, tm12049, ep12049, em12049, dsL]
  · norm_num [world12049, agent12049, scalar12049, tp12049, tm12049, ep12049, em12049, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12049, agent12049, tp12049, tm12049, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12049, agent12049, scalar12049, tp12049, tm12049, ep12049, em12049, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12049, agent12049, tp12049, tm12049, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12049, agent12049, scalar12049, tp12049, tm12049, ep12049, em12049, dsL]

theorem negative12049 :
    Eminus aL (agent12049.root+dsL) scalar12049.worldRadius world12049.frame
      agent12049.frame tm12049 ≤ -em12049 := by
  apply negative_check (lo := (67809189643758301291 / 100000000000000000000)) (hi := (16952297410939575323 / 25000000000000000000))
    (y := (-((3667110556531703963 / 5000000000000000000)))) (u := (48026266245145782849 / 100000000000000000000))
  · norm_num [world12049, agent12049, scalar12049, tp12049, tm12049, ep12049, em12049, dsL]
  · norm_num [world12049, agent12049, scalar12049, tp12049, tm12049, ep12049, em12049, dsL]
  · norm_num [world12049, agent12049, scalar12049, tp12049, tm12049, ep12049, em12049, dsL]
  · norm_num [world12049, agent12049, scalar12049, tp12049, tm12049, ep12049, em12049, dsL]
  · norm_num [world12049, agent12049, scalar12049, tp12049, tm12049, ep12049, em12049, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12049, agent12049, tp12049, tm12049, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12049, agent12049, tp12049, tm12049, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12049, agent12049, scalar12049, tp12049, tm12049, ep12049, em12049, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12049, agent12049, tp12049, tm12049, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12049, agent12049, scalar12049, tp12049, tm12049, ep12049, em12049, dsL]

theorem tails12049 :
    exp (-((12049:ℝ)*ep12049)) ≤ scalar12049.upperTail ∧
    exp (-((12049:ℝ)*em12049)) ≤ scalar12049.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12049:ℝ)) (by norm_num [ep12049]) ?_)
      (show bp12049^8 ≤ scalar12049.upperTail by norm_num [bp12049, scalar12049])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12049, bp12049, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12049:ℝ)) (by norm_num [em12049]) ?_)
      (show bm12049^8 ≤ scalar12049.lowerTail by norm_num [bm12049, scalar12049])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12049, bm12049, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12049 :
    agent12049.root+dsL+scalar12049.worldRadius < √(1/100/aL) ∧
    2*(agent12049.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12049, agent12049, scalar12049, tp12049, tm12049, ep12049, em12049, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12049, agent12049, scalar12049, tp12049, tm12049, ep12049, em12049, dsL]

noncomputable def master12049 : MasterCertificate 12049 world12049 agent12049 :=
  master scalar12049 dsL tp12049 tm12049 ep12049 em12049
    (by norm_num [dsL]) (by norm_num [tp12049]) (by norm_num [tm12049])
    (by norm_num [ep12049]) (by norm_num [em12049])
    positive12049 negative12049 tails12049.1 tails12049.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12049.1 tailGuards12049.2

theorem preserves12049 : master12049.toScalarCertificate = scalar12049 := rfl

noncomputable def tp12050 : ℝ := (2362938433 / 10000000000)
noncomputable def tm12050 : ℝ := (-((6116587471 / 10000000000)))
noncomputable def ep12050 : ℝ := (1086058335938483 / 2000000000000000000)
noncomputable def em12050 : ℝ := (52384416096679131 / 100000000000000000000)
noncomputable def bp12050 : ℝ := (44134090089658031693 / 100000000000000000000)
noncomputable def bm12050 : ℝ := (113570143496065273 / 250000000000000000)

theorem positive12050 :
    Eplus aL (agent12050.root+dsL) scalar12050.worldRadius world12050.frame
      agent12050.frame tp12050 ≤ -ep12050 := by
  apply positive_check (eT := (23238435573547850401 / 20000000000000000000)) (y := (39562710979280839757 / 100000000000000000000)) (u := (29706307094475679523 / 20000000000000000000))
  · norm_num [world12050, agent12050, scalar12050, tp12050, tm12050, ep12050, em12050, dsL]
  · norm_num [world12050, agent12050, scalar12050, tp12050, tm12050, ep12050, em12050, dsL]
  · norm_num [world12050, agent12050, scalar12050, tp12050, tm12050, ep12050, em12050, dsL]
  · norm_num [world12050, agent12050, scalar12050, tp12050, tm12050, ep12050, em12050, dsL]
  · norm_num [world12050, agent12050, scalar12050, tp12050, tm12050, ep12050, em12050, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12050, agent12050, tp12050, tm12050, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12050, agent12050, scalar12050, tp12050, tm12050, ep12050, em12050, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12050, agent12050, tp12050, tm12050, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12050, agent12050, scalar12050, tp12050, tm12050, ep12050, em12050, dsL]

theorem negative12050 :
    Eminus aL (agent12050.root+dsL) scalar12050.worldRadius world12050.frame
      agent12050.frame tm12050 ≤ -em12050 := by
  apply negative_check (lo := (678088326732302047 / 1000000000000000000)) (hi := (67808832673230204701 / 100000000000000000000))
    (y := (-((73341846018836560551 / 100000000000000000000)))) (u := (6003305199378732873 / 12500000000000000000))
  · norm_num [world12050, agent12050, scalar12050, tp12050, tm12050, ep12050, em12050, dsL]
  · norm_num [world12050, agent12050, scalar12050, tp12050, tm12050, ep12050, em12050, dsL]
  · norm_num [world12050, agent12050, scalar12050, tp12050, tm12050, ep12050, em12050, dsL]
  · norm_num [world12050, agent12050, scalar12050, tp12050, tm12050, ep12050, em12050, dsL]
  · norm_num [world12050, agent12050, scalar12050, tp12050, tm12050, ep12050, em12050, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12050, agent12050, tp12050, tm12050, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12050, agent12050, tp12050, tm12050, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12050, agent12050, scalar12050, tp12050, tm12050, ep12050, em12050, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12050, agent12050, tp12050, tm12050, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12050, agent12050, scalar12050, tp12050, tm12050, ep12050, em12050, dsL]

theorem tails12050 :
    exp (-((12050:ℝ)*ep12050)) ≤ scalar12050.upperTail ∧
    exp (-((12050:ℝ)*em12050)) ≤ scalar12050.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12050:ℝ)) (by norm_num [ep12050]) ?_)
      (show bp12050^8 ≤ scalar12050.upperTail by norm_num [bp12050, scalar12050])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12050, bp12050, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12050:ℝ)) (by norm_num [em12050]) ?_)
      (show bm12050^8 ≤ scalar12050.lowerTail by norm_num [bm12050, scalar12050])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12050, bm12050, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12050 :
    agent12050.root+dsL+scalar12050.worldRadius < √(1/100/aL) ∧
    2*(agent12050.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12050, agent12050, scalar12050, tp12050, tm12050, ep12050, em12050, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12050, agent12050, scalar12050, tp12050, tm12050, ep12050, em12050, dsL]

noncomputable def master12050 : MasterCertificate 12050 world12050 agent12050 :=
  master scalar12050 dsL tp12050 tm12050 ep12050 em12050
    (by norm_num [dsL]) (by norm_num [tp12050]) (by norm_num [tm12050])
    (by norm_num [ep12050]) (by norm_num [em12050])
    positive12050 negative12050 tails12050.1 tails12050.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12050.1 tailGuards12050.2

theorem preserves12050 : master12050.toScalarCertificate = scalar12050 := rfl

noncomputable def tp12051 : ℝ := (2363041229 / 10000000000)
noncomputable def tm12051 : ℝ := (-((6116818717 / 10000000000)))
noncomputable def ep12051 : ℝ := (54305951116823063 / 100000000000000000000)
noncomputable def em12051 : ℝ := (26193530111761637 / 50000000000000000000)
noncomputable def bp12051 : ℝ := (11032269330164037863 / 25000000000000000000)
noncomputable def bm12051 : ℝ := (45423273576814259727 / 100000000000000000000)

theorem positive12051 :
    Eplus aL (agent12051.root+dsL) scalar12051.worldRadius world12051.frame
      agent12051.frame tp12051 ≤ -ep12051 := by
  apply positive_check (eT := (116192513199691433909 / 100000000000000000000)) (y := (19781687662230024639 / 50000000000000000000)) (u := (29706504447550334941 / 20000000000000000000))
  · norm_num [world12051, agent12051, scalar12051, tp12051, tm12051, ep12051, em12051, dsL]
  · norm_num [world12051, agent12051, scalar12051, tp12051, tm12051, ep12051, em12051, dsL]
  · norm_num [world12051, agent12051, scalar12051, tp12051, tm12051, ep12051, em12051, dsL]
  · norm_num [world12051, agent12051, scalar12051, tp12051, tm12051, ep12051, em12051, dsL]
  · norm_num [world12051, agent12051, scalar12051, tp12051, tm12051, ep12051, em12051, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12051, agent12051, tp12051, tm12051, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12051, agent12051, scalar12051, tp12051, tm12051, ep12051, em12051, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12051, agent12051, tp12051, tm12051, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12051, agent12051, scalar12051, tp12051, tm12051, ep12051, em12051, dsL]

theorem negative12051 :
    Eminus aL (agent12051.root+dsL) scalar12051.worldRadius world12051.frame
      agent12051.frame tm12051 ≤ -em12051 := by
  apply negative_check (lo := (33904238086625036577 / 50000000000000000000)) (hi := (13561695234650014631 / 20000000000000000000))
    (y := (-((73341480566208872471 / 100000000000000000000)))) (u := (48026617109243367559 / 100000000000000000000))
  · norm_num [world12051, agent12051, scalar12051, tp12051, tm12051, ep12051, em12051, dsL]
  · norm_num [world12051, agent12051, scalar12051, tp12051, tm12051, ep12051, em12051, dsL]
  · norm_num [world12051, agent12051, scalar12051, tp12051, tm12051, ep12051, em12051, dsL]
  · norm_num [world12051, agent12051, scalar12051, tp12051, tm12051, ep12051, em12051, dsL]
  · norm_num [world12051, agent12051, scalar12051, tp12051, tm12051, ep12051, em12051, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12051, agent12051, tp12051, tm12051, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12051, agent12051, tp12051, tm12051, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12051, agent12051, scalar12051, tp12051, tm12051, ep12051, em12051, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12051, agent12051, tp12051, tm12051, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12051, agent12051, scalar12051, tp12051, tm12051, ep12051, em12051, dsL]

theorem tails12051 :
    exp (-((12051:ℝ)*ep12051)) ≤ scalar12051.upperTail ∧
    exp (-((12051:ℝ)*em12051)) ≤ scalar12051.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12051:ℝ)) (by norm_num [ep12051]) ?_)
      (show bp12051^8 ≤ scalar12051.upperTail by norm_num [bp12051, scalar12051])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12051, bp12051, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12051:ℝ)) (by norm_num [em12051]) ?_)
      (show bm12051^8 ≤ scalar12051.lowerTail by norm_num [bm12051, scalar12051])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12051, bm12051, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12051 :
    agent12051.root+dsL+scalar12051.worldRadius < √(1/100/aL) ∧
    2*(agent12051.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12051, agent12051, scalar12051, tp12051, tm12051, ep12051, em12051, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12051, agent12051, scalar12051, tp12051, tm12051, ep12051, em12051, dsL]

noncomputable def master12051 : MasterCertificate 12051 world12051 agent12051 :=
  master scalar12051 dsL tp12051 tm12051 ep12051 em12051
    (by norm_num [dsL]) (by norm_num [tp12051]) (by norm_num [tm12051])
    (by norm_num [ep12051]) (by norm_num [em12051])
    positive12051 negative12051 tails12051.1 tails12051.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12051.1 tailGuards12051.2

theorem preserves12051 : master12051.toScalarCertificate = scalar12051 := rfl

noncomputable def tp12052 : ℝ := (590786001 / 2500000000)
noncomputable def tm12052 : ℝ := (-((3058524869 / 5000000000)))
noncomputable def ep12052 : ℝ := (13577245918501623 / 25000000000000000000)
noncomputable def em12052 : ℝ := (26194851355091257 / 50000000000000000000)
noncomputable def bp12052 : ℝ := (44124065958018597309 / 100000000000000000000)
noncomputable def bm12052 : ℝ := (22709245540498612889 / 50000000000000000000)

theorem positive12052 :
    Eplus aL (agent12052.root+dsL) scalar12052.worldRadius world12052.frame
      agent12052.frame tp12052 ≤ -ep12052 := by
  apply positive_check (eT := (58096424206599992319 / 50000000000000000000)) (y := (39564040109831548973 / 100000000000000000000)) (u := (148533509663513558183 / 100000000000000000000))
  · norm_num [world12052, agent12052, scalar12052, tp12052, tm12052, ep12052, em12052, dsL]
  · norm_num [world12052, agent12052, scalar12052, tp12052, tm12052, ep12052, em12052, dsL]
  · norm_num [world12052, agent12052, scalar12052, tp12052, tm12052, ep12052, em12052, dsL]
  · norm_num [world12052, agent12052, scalar12052, tp12052, tm12052, ep12052, em12052, dsL]
  · norm_num [world12052, agent12052, scalar12052, tp12052, tm12052, ep12052, em12052, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12052, agent12052, tp12052, tm12052, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12052, agent12052, scalar12052, tp12052, tm12052, ep12052, em12052, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12052, agent12052, tp12052, tm12052, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12052, agent12052, scalar12052, tp12052, tm12052, ep12052, em12052, dsL]

theorem negative12052 :
    Eminus aL (agent12052.root+dsL) scalar12052.worldRadius world12052.frame
      agent12052.frame tm12052 ≤ -em12052 := by
  apply negative_check (lo := (3390406029154925249 / 5000000000000000000)) (hi := (67808120583098504981 / 100000000000000000000))
    (y := (-((36670557309231341117 / 50000000000000000000)))) (u := (1921071714475513259 / 4000000000000000000))
  · norm_num [world12052, agent12052, scalar12052, tp12052, tm12052, ep12052, em12052, dsL]
  · norm_num [world12052, agent12052, scalar12052, tp12052, tm12052, ep12052, em12052, dsL]
  · norm_num [world12052, agent12052, scalar12052, tp12052, tm12052, ep12052, em12052, dsL]
  · norm_num [world12052, agent12052, scalar12052, tp12052, tm12052, ep12052, em12052, dsL]
  · norm_num [world12052, agent12052, scalar12052, tp12052, tm12052, ep12052, em12052, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12052, agent12052, tp12052, tm12052, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12052, agent12052, tp12052, tm12052, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12052, agent12052, scalar12052, tp12052, tm12052, ep12052, em12052, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12052, agent12052, tp12052, tm12052, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12052, agent12052, scalar12052, tp12052, tm12052, ep12052, em12052, dsL]

theorem tails12052 :
    exp (-((12052:ℝ)*ep12052)) ≤ scalar12052.upperTail ∧
    exp (-((12052:ℝ)*em12052)) ≤ scalar12052.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12052:ℝ)) (by norm_num [ep12052]) ?_)
      (show bp12052^8 ≤ scalar12052.upperTail by norm_num [bp12052, scalar12052])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12052, bp12052, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12052:ℝ)) (by norm_num [em12052]) ?_)
      (show bm12052^8 ≤ scalar12052.lowerTail by norm_num [bm12052, scalar12052])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12052, bm12052, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12052 :
    agent12052.root+dsL+scalar12052.worldRadius < √(1/100/aL) ∧
    2*(agent12052.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12052, agent12052, scalar12052, tp12052, tm12052, ep12052, em12052, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12052, agent12052, scalar12052, tp12052, tm12052, ep12052, em12052, dsL]

noncomputable def master12052 : MasterCertificate 12052 world12052 agent12052 :=
  master scalar12052 dsL tp12052 tm12052 ep12052 em12052
    (by norm_num [dsL]) (by norm_num [tp12052]) (by norm_num [tm12052])
    (by norm_num [ep12052]) (by norm_num [em12052])
    positive12052 negative12052 tails12052.1 tails12052.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12052.1 tailGuards12052.2

theorem preserves12052 : master12052.toScalarCertificate = scalar12052 := rfl

noncomputable def tp12053 : ℝ := (472649393 / 2000000000)
noncomputable def tm12053 : ℝ := (-((6117281361 / 10000000000)))
noncomputable def ep12053 : ℝ := (13578004939767941 / 25000000000000000000)
noncomputable def em12053 : ℝ := (10478469836371047 / 20000000000000000000)
noncomputable def bp12053 : ℝ := (8823810496996220683 / 20000000000000000000)
noncomputable def bm12053 : ℝ := (45413706062100584773 / 100000000000000000000)

theorem positive12053 :
    Eplus aL (agent12053.root+dsL) scalar12053.worldRadius world12053.frame
      agent12053.frame tp12053 ≤ -ep12053 := by
  apply positive_check (eT := (116193185035767333307 / 100000000000000000000)) (y := (39564701973926091079 / 100000000000000000000)) (u := (74267246378367875573 / 50000000000000000000))
  · norm_num [world12053, agent12053, scalar12053, tp12053, tm12053, ep12053, em12053, dsL]
  · norm_num [world12053, agent12053, scalar12053, tp12053, tm12053, ep12053, em12053, dsL]
  · norm_num [world12053, agent12053, scalar12053, tp12053, tm12053, ep12053, em12053, dsL]
  · norm_num [world12053, agent12053, scalar12053, tp12053, tm12053, ep12053, em12053, dsL]
  · norm_num [world12053, agent12053, scalar12053, tp12053, tm12053, ep12053, em12053, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12053, agent12053, tp12053, tm12053, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12053, agent12053, scalar12053, tp12053, tm12053, ep12053, em12053, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12053, agent12053, tp12053, tm12053, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12053, agent12053, scalar12053, tp12053, tm12053, ep12053, em12053, dsL]

theorem negative12053 :
    Eminus aL (agent12053.root+dsL) scalar12053.worldRadius world12053.frame
      agent12053.frame tm12053 ≤ -em12053 := by
  apply negative_check (lo := (16951940585341114307 / 25000000000000000000)) (hi := (67807762341364457229 / 100000000000000000000))
    (y := (-((73340742017706905993 / 100000000000000000000)))) (u := (48026971810414391533 / 100000000000000000000))
  · norm_num [world12053, agent12053, scalar12053, tp12053, tm12053, ep12053, em12053, dsL]
  · norm_num [world12053, agent12053, scalar12053, tp12053, tm12053, ep12053, em12053, dsL]
  · norm_num [world12053, agent12053, scalar12053, tp12053, tm12053, ep12053, em12053, dsL]
  · norm_num [world12053, agent12053, scalar12053, tp12053, tm12053, ep12053, em12053, dsL]
  · norm_num [world12053, agent12053, scalar12053, tp12053, tm12053, ep12053, em12053, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12053, agent12053, tp12053, tm12053, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12053, agent12053, tp12053, tm12053, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12053, agent12053, scalar12053, tp12053, tm12053, ep12053, em12053, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12053, agent12053, tp12053, tm12053, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12053, agent12053, scalar12053, tp12053, tm12053, ep12053, em12053, dsL]

theorem tails12053 :
    exp (-((12053:ℝ)*ep12053)) ≤ scalar12053.upperTail ∧
    exp (-((12053:ℝ)*em12053)) ≤ scalar12053.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12053:ℝ)) (by norm_num [ep12053]) ?_)
      (show bp12053^8 ≤ scalar12053.upperTail by norm_num [bp12053, scalar12053])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12053, bp12053, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12053:ℝ)) (by norm_num [em12053]) ?_)
      (show bm12053^8 ≤ scalar12053.lowerTail by norm_num [bm12053, scalar12053])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12053, bm12053, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12053 :
    agent12053.root+dsL+scalar12053.worldRadius < √(1/100/aL) ∧
    2*(agent12053.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12053, agent12053, scalar12053, tp12053, tm12053, ep12053, em12053, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12053, agent12053, scalar12053, tp12053, tm12053, ep12053, em12053, dsL]

noncomputable def master12053 : MasterCertificate 12053 world12053 agent12053 :=
  master scalar12053 dsL tp12053 tm12053 ep12053 em12053
    (by norm_num [dsL]) (by norm_num [tp12053]) (by norm_num [tm12053])
    (by norm_num [ep12053]) (by norm_num [em12053])
    positive12053 negative12053 tails12053.1 tails12053.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12053.1 tailGuards12053.2

theorem preserves12053 : master12053.toScalarCertificate = scalar12053 := rfl

noncomputable def tp12054 : ℝ := (2363349907 / 10000000000)
noncomputable def tm12054 : ℝ := (-((305875661 / 500000000)))
noncomputable def ep12054 : ℝ := (54315055763216151 / 100000000000000000000)
noncomputable def em12054 : ℝ := (6549374474730673 / 12500000000000000000)
noncomputable def bp12054 : ℝ := (4411403930053762297 / 10000000000000000000)
noncomputable def bm12054 : ℝ := (45408921148149350173 / 100000000000000000000)

theorem positive12054 :
    Eplus aL (agent12054.root+dsL) scalar12054.worldRadius world12054.frame
      agent12054.frame tp12054 ≤ -ep12054 := by
  apply positive_check (eT := (11619352155459565949 / 10000000000000000000)) (y := (4945670252463179887 / 12500000000000000000)) (u := (148535473155621605141 / 100000000000000000000))
  · norm_num [world12054, agent12054, scalar12054, tp12054, tm12054, ep12054, em12054, dsL]
  · norm_num [world12054, agent12054, scalar12054, tp12054, tm12054, ep12054, em12054, dsL]
  · norm_num [world12054, agent12054, scalar12054, tp12054, tm12054, ep12054, em12054, dsL]
  · norm_num [world12054, agent12054, scalar12054, tp12054, tm12054, ep12054, em12054, dsL]
  · norm_num [world12054, agent12054, scalar12054, tp12054, tm12054, ep12054, em12054, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12054, agent12054, tp12054, tm12054, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12054, agent12054, scalar12054, tp12054, tm12054, ep12054, em12054, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12054, agent12054, tp12054, tm12054, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12054, agent12054, scalar12054, tp12054, tm12054, ep12054, em12054, dsL]

theorem negative12054 :
    Eminus aL (agent12054.root+dsL) scalar12054.worldRadius world12054.frame
      agent12054.frame tm12054 ≤ -em12054 := by
  apply negative_check (lo := (33903701512184273827 / 50000000000000000000)) (hi := (13561480604873709531 / 20000000000000000000))
    (y := (-((73340368742983171951 / 100000000000000000000)))) (u := (960543021665906493 / 2000000000000000000))
  · norm_num [world12054, agent12054, scalar12054, tp12054, tm12054, ep12054, em12054, dsL]
  · norm_num [world12054, agent12054, scalar12054, tp12054, tm12054, ep12054, em12054, dsL]
  · norm_num [world12054, agent12054, scalar12054, tp12054, tm12054, ep12054, em12054, dsL]
  · norm_num [world12054, agent12054, scalar12054, tp12054, tm12054, ep12054, em12054, dsL]
  · norm_num [world12054, agent12054, scalar12054, tp12054, tm12054, ep12054, em12054, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12054, agent12054, tp12054, tm12054, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12054, agent12054, tp12054, tm12054, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12054, agent12054, scalar12054, tp12054, tm12054, ep12054, em12054, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12054, agent12054, tp12054, tm12054, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12054, agent12054, scalar12054, tp12054, tm12054, ep12054, em12054, dsL]

theorem tails12054 :
    exp (-((12054:ℝ)*ep12054)) ≤ scalar12054.upperTail ∧
    exp (-((12054:ℝ)*em12054)) ≤ scalar12054.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12054:ℝ)) (by norm_num [ep12054]) ?_)
      (show bp12054^8 ≤ scalar12054.upperTail by norm_num [bp12054, scalar12054])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12054, bp12054, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12054:ℝ)) (by norm_num [em12054]) ?_)
      (show bm12054^8 ≤ scalar12054.lowerTail by norm_num [bm12054, scalar12054])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12054, bm12054, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12054 :
    agent12054.root+dsL+scalar12054.worldRadius < √(1/100/aL) ∧
    2*(agent12054.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12054, agent12054, scalar12054, tp12054, tm12054, ep12054, em12054, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12054, agent12054, scalar12054, tp12054, tm12054, ep12054, em12054, dsL]

noncomputable def master12054 : MasterCertificate 12054 world12054 agent12054 :=
  master scalar12054 dsL tp12054 tm12054 ep12054 em12054
    (by norm_num [dsL]) (by norm_num [tp12054]) (by norm_num [tm12054])
    (by norm_num [ep12054]) (by norm_num [em12054])
    positive12054 negative12054 tails12054.1 tails12054.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12054.1 tailGuards12054.2

theorem preserves12054 : master12054.toScalarCertificate = scalar12054 := rfl

noncomputable def tp12055 : ℝ := (118172641 / 500000000)
noncomputable def tm12055 : ℝ := (-((305887241 / 500000000)))
noncomputable def ep12055 : ℝ := (13579522337301381 / 25000000000000000000)
noncomputable def em12055 : ℝ := (1309941005157743 / 2500000000000000000)
noncomputable def bp12055 : ℝ := (22054513979108565179 / 50000000000000000000)
noncomputable def bm12055 : ℝ := (4540413794828456871 / 10000000000000000000)

theorem positive12055 :
    Eplus aL (agent12055.root+dsL) scalar12055.worldRadius world12055.frame
      agent12055.frame tp12055 ≤ -ep12055 := by
  apply positive_check (eT := (58096928947943985179 / 50000000000000000000)) (y := (19783011071811322903 / 50000000000000000000)) (u := (74268226838520883097 / 50000000000000000000))
  · norm_num [world12055, agent12055, scalar12055, tp12055, tm12055, ep12055, em12055, dsL]
  · norm_num [world12055, agent12055, scalar12055, tp12055, tm12055, ep12055, em12055, dsL]
  · norm_num [world12055, agent12055, scalar12055, tp12055, tm12055, ep12055, em12055, dsL]
  · norm_num [world12055, agent12055, scalar12055, tp12055, tm12055, ep12055, em12055, dsL]
  · norm_num [world12055, agent12055, scalar12055, tp12055, tm12055, ep12055, em12055, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12055, agent12055, tp12055, tm12055, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12055, agent12055, scalar12055, tp12055, tm12055, ep12055, em12055, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12055, agent12055, tp12055, tm12055, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12055, agent12055, scalar12055, tp12055, tm12055, ep12055, em12055, dsL]

theorem negative12055 :
    Eminus aL (agent12055.root+dsL) scalar12055.worldRadius world12055.frame
      agent12055.frame tm12055 ≤ -em12055 := by
  apply negative_check (lo := (67807044763725567681 / 100000000000000000000)) (hi := (33903522381862783841 / 50000000000000000000))
    (y := (-((18334998446536895383 / 25000000000000000000)))) (u := (48027331164718864397 / 100000000000000000000))
  · norm_num [world12055, agent12055, scalar12055, tp12055, tm12055, ep12055, em12055, dsL]
  · norm_num [world12055, agent12055, scalar12055, tp12055, tm12055, ep12055, em12055, dsL]
  · norm_num [world12055, agent12055, scalar12055, tp12055, tm12055, ep12055, em12055, dsL]
  · norm_num [world12055, agent12055, scalar12055, tp12055, tm12055, ep12055, em12055, dsL]
  · norm_num [world12055, agent12055, scalar12055, tp12055, tm12055, ep12055, em12055, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12055, agent12055, tp12055, tm12055, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12055, agent12055, tp12055, tm12055, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12055, agent12055, scalar12055, tp12055, tm12055, ep12055, em12055, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12055, agent12055, tp12055, tm12055, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12055, agent12055, scalar12055, tp12055, tm12055, ep12055, em12055, dsL]

theorem tails12055 :
    exp (-((12055:ℝ)*ep12055)) ≤ scalar12055.upperTail ∧
    exp (-((12055:ℝ)*em12055)) ≤ scalar12055.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12055:ℝ)) (by norm_num [ep12055]) ?_)
      (show bp12055^8 ≤ scalar12055.upperTail by norm_num [bp12055, scalar12055])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12055, bp12055, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12055:ℝ)) (by norm_num [em12055]) ?_)
      (show bm12055^8 ≤ scalar12055.lowerTail by norm_num [bm12055, scalar12055])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12055, bm12055, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12055 :
    agent12055.root+dsL+scalar12055.worldRadius < √(1/100/aL) ∧
    2*(agent12055.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12055, agent12055, scalar12055, tp12055, tm12055, ep12055, em12055, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12055, agent12055, scalar12055, tp12055, tm12055, ep12055, em12055, dsL]

noncomputable def master12055 : MasterCertificate 12055 world12055 agent12055 :=
  master scalar12055 dsL tp12055 tm12055 ep12055 em12055
    (by norm_num [dsL]) (by norm_num [tp12055]) (by norm_num [tm12055])
    (by norm_num [ep12055]) (by norm_num [em12055])
    positive12055 negative12055 tails12055.1 tails12055.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12055.1 tailGuards12055.2

theorem preserves12055 : master12055.toScalarCertificate = scalar12055 := rfl

noncomputable def tp12056 : ℝ := (2363555677 / 10000000000)
noncomputable def tm12056 : ℝ := (-((6117976269 / 10000000000)))
noncomputable def ep12056 : ℝ := (54321121434003749 / 100000000000000000000)
noncomputable def em12056 : ℝ := (13100070789946743 / 25000000000000000000)
noncomputable def bp12056 : ℝ := (44104017848463385879 / 100000000000000000000)
noncomputable def bm12056 : ℝ := (45399355947583456599 / 100000000000000000000)

theorem positive12056 :
    Eplus aL (agent12056.root+dsL) scalar12056.worldRadius world12056.frame
      agent12056.frame tp12056 ≤ -ep12056 := by
  apply positive_check (eT := (58097096930235546499 / 50000000000000000000)) (y := (9891670532247759689 / 25000000000000000000)) (u := (74268716999568876041 / 50000000000000000000))
  · norm_num [world12056, agent12056, scalar12056, tp12056, tm12056, ep12056, em12056, dsL]
  · norm_num [world12056, agent12056, scalar12056, tp12056, tm12056, ep12056, em12056, dsL]
  · norm_num [world12056, agent12056, scalar12056, tp12056, tm12056, ep12056, em12056, dsL]
  · norm_num [world12056, agent12056, scalar12056, tp12056, tm12056, ep12056, em12056, dsL]
  · norm_num [world12056, agent12056, scalar12056, tp12056, tm12056, ep12056, em12056, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12056, agent12056, tp12056, tm12056, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12056, agent12056, scalar12056, tp12056, tm12056, ep12056, em12056, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12056, agent12056, tp12056, tm12056, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12056, agent12056, scalar12056, tp12056, tm12056, ep12056, em12056, dsL]

theorem negative12056 :
    Eminus aL (agent12056.root+dsL) scalar12056.worldRadius world12056.frame
      agent12056.frame tm12056 ≤ -em12056 := by
  apply negative_check (lo := (67806687094244081629 / 100000000000000000000)) (hi := (6780668709424408163 / 10000000000000000000))
    (y := (-((36669809467808423551 / 50000000000000000000)))) (u := (48027511195762056377 / 100000000000000000000))
  · norm_num [world12056, agent12056, scalar12056, tp12056, tm12056, ep12056, em12056, dsL]
  · norm_num [world12056, agent12056, scalar12056, tp12056, tm12056, ep12056, em12056, dsL]
  · norm_num [world12056, agent12056, scalar12056, tp12056, tm12056, ep12056, em12056, dsL]
  · norm_num [world12056, agent12056, scalar12056, tp12056, tm12056, ep12056, em12056, dsL]
  · norm_num [world12056, agent12056, scalar12056, tp12056, tm12056, ep12056, em12056, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12056, agent12056, tp12056, tm12056, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12056, agent12056, tp12056, tm12056, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12056, agent12056, scalar12056, tp12056, tm12056, ep12056, em12056, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12056, agent12056, tp12056, tm12056, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12056, agent12056, scalar12056, tp12056, tm12056, ep12056, em12056, dsL]

theorem tails12056 :
    exp (-((12056:ℝ)*ep12056)) ≤ scalar12056.upperTail ∧
    exp (-((12056:ℝ)*em12056)) ≤ scalar12056.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12056:ℝ)) (by norm_num [ep12056]) ?_)
      (show bp12056^8 ≤ scalar12056.upperTail by norm_num [bp12056, scalar12056])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12056, bp12056, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12056:ℝ)) (by norm_num [em12056]) ?_)
      (show bm12056^8 ≤ scalar12056.lowerTail by norm_num [bm12056, scalar12056])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12056, bm12056, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12056 :
    agent12056.root+dsL+scalar12056.worldRadius < √(1/100/aL) ∧
    2*(agent12056.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12056, agent12056, scalar12056, tp12056, tm12056, ep12056, em12056, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12056, agent12056, scalar12056, tp12056, tm12056, ep12056, em12056, dsL]

noncomputable def master12056 : MasterCertificate 12056 world12056 agent12056 :=
  master scalar12056 dsL tp12056 tm12056 ep12056 em12056
    (by norm_num [dsL]) (by norm_num [tp12056]) (by norm_num [tm12056])
    (by norm_num [ep12056]) (by norm_num [em12056])
    positive12056 negative12056 tails12056.1 tails12056.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12056.1 tailGuards12056.2

theorem preserves12056 : master12056.toScalarCertificate = scalar12056 := rfl

noncomputable def tp12057 : ℝ := (1181829271 / 5000000000)
noncomputable def tm12057 : ℝ := (-((1529551949 / 2500000000)))
noncomputable def ep12057 : ℝ := (13581038110238109 / 25000000000000000000)
noncomputable def em12057 : ℝ := (26201462555080823 / 50000000000000000000)
noncomputable def bp12057 : ℝ := (11024752172467403509 / 25000000000000000000)
noncomputable def bm12057 : ℝ := (45394574836862792703 / 100000000000000000000)

theorem positive12057 :
    Eplus aL (agent12057.root+dsL) scalar12057.worldRadius world12057.frame
      agent12057.frame tp12057 ≤ -ep12057 := by
  apply positive_check (eT := (29048632480130929179 / 25000000000000000000)) (y := (39567342756442353239 / 100000000000000000000)) (u := (148538415281443535093 / 100000000000000000000))
  · norm_num [world12057, agent12057, scalar12057, tp12057, tm12057, ep12057, em12057, dsL]
  · norm_num [world12057, agent12057, scalar12057, tp12057, tm12057, ep12057, em12057, dsL]
  · norm_num [world12057, agent12057, scalar12057, tp12057, tm12057, ep12057, em12057, dsL]
  · norm_num [world12057, agent12057, scalar12057, tp12057, tm12057, ep12057, em12057, dsL]
  · norm_num [world12057, agent12057, scalar12057, tp12057, tm12057, ep12057, em12057, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12057, agent12057, tp12057, tm12057, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12057, agent12057, scalar12057, tp12057, tm12057, ep12057, em12057, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12057, agent12057, tp12057, tm12057, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12057, agent12057, scalar12057, tp12057, tm12057, ep12057, em12057, dsL]

theorem negative12057 :
    Eminus aL (agent12057.root+dsL) scalar12057.worldRadius world12057.frame
      agent12057.frame tm12057 ≤ -em12057 := by
  apply negative_check (lo := (13561265805990460597 / 20000000000000000000)) (hi := (33903164514976151493 / 50000000000000000000))
    (y := (-((572962859137128983 / 781250000000000000)))) (u := (24013845161207201481 / 50000000000000000000))
  · norm_num [world12057, agent12057, scalar12057, tp12057, tm12057, ep12057, em12057, dsL]
  · norm_num [world12057, agent12057, scalar12057, tp12057, tm12057, ep12057, em12057, dsL]
  · norm_num [world12057, agent12057, scalar12057, tp12057, tm12057, ep12057, em12057, dsL]
  · norm_num [world12057, agent12057, scalar12057, tp12057, tm12057, ep12057, em12057, dsL]
  · norm_num [world12057, agent12057, scalar12057, tp12057, tm12057, ep12057, em12057, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12057, agent12057, tp12057, tm12057, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12057, agent12057, tp12057, tm12057, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12057, agent12057, scalar12057, tp12057, tm12057, ep12057, em12057, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12057, agent12057, tp12057, tm12057, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12057, agent12057, scalar12057, tp12057, tm12057, ep12057, em12057, dsL]

theorem tails12057 :
    exp (-((12057:ℝ)*ep12057)) ≤ scalar12057.upperTail ∧
    exp (-((12057:ℝ)*em12057)) ≤ scalar12057.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12057:ℝ)) (by norm_num [ep12057]) ?_)
      (show bp12057^8 ≤ scalar12057.upperTail by norm_num [bp12057, scalar12057])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12057, bp12057, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12057:ℝ)) (by norm_num [em12057]) ?_)
      (show bm12057^8 ≤ scalar12057.lowerTail by norm_num [bm12057, scalar12057])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12057, bm12057, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12057 :
    agent12057.root+dsL+scalar12057.worldRadius < √(1/100/aL) ∧
    2*(agent12057.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12057, agent12057, scalar12057, tp12057, tm12057, ep12057, em12057, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12057, agent12057, scalar12057, tp12057, tm12057, ep12057, em12057, dsL]

noncomputable def master12057 : MasterCertificate 12057 world12057 agent12057 :=
  master scalar12057 dsL tp12057 tm12057 ep12057 em12057
    (by norm_num [dsL]) (by norm_num [tp12057]) (by norm_num [tm12057])
    (by norm_num [ep12057]) (by norm_num [em12057])
    positive12057 negative12057 tails12057.1 tails12057.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12057.1 tailGuards12057.2

theorem preserves12057 : master12057.toScalarCertificate = scalar12057 := rfl

noncomputable def tp12058 : ℝ := (23637613 / 100000000)
noncomputable def tm12058 : ℝ := (-((6118438947 / 10000000000)))
noncomputable def ep12058 : ℝ := (3395448818383043 / 6250000000000000000)
noncomputable def em12058 : ℝ := (10481112969901869 / 20000000000000000000)
noncomputable def bp12058 : ℝ := (22047000665203142063 / 50000000000000000000)
noncomputable def bm12058 : ℝ := (11347448860626204017 / 25000000000000000000)

theorem positive12058 :
    Eplus aL (agent12058.root+dsL) scalar12058.worldRadius world12058.frame
      agent12058.frame tp12058 ≤ -ep12058 := by
  apply positive_check (eT := (116194865227540916201 / 100000000000000000000)) (y := (39568002375623660113 / 100000000000000000000)) (u := (148539395072553782253 / 100000000000000000000))
  · norm_num [world12058, agent12058, scalar12058, tp12058, tm12058, ep12058, em12058, dsL]
  · norm_num [world12058, agent12058, scalar12058, tp12058, tm12058, ep12058, em12058, dsL]
  · norm_num [world12058, agent12058, scalar12058, tp12058, tm12058, ep12058, em12058, dsL]
  · norm_num [world12058, agent12058, scalar12058, tp12058, tm12058, ep12058, em12058, dsL]
  · norm_num [world12058, agent12058, scalar12058, tp12058, tm12058, ep12058, em12058, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12058, agent12058, tp12058, tm12058, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12058, agent12058, scalar12058, tp12058, tm12058, ep12058, em12058, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12058, agent12058, tp12058, tm12058, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12058, agent12058, scalar12058, tp12058, tm12058, ep12058, em12058, dsL]

theorem negative12058 :
    Eminus aL (agent12058.root+dsL) scalar12058.worldRadius world12058.frame
      agent12058.frame tm12058 ≤ -em12058 := by
  apply negative_check (lo := (33902986262821012687 / 50000000000000000000)) (hi := (542447780205136203 / 800000000000000000))
    (y := (-((36669435384088029577 / 50000000000000000000)))) (u := (4802787052330762803 / 10000000000000000000))
  · norm_num [world12058, agent12058, scalar12058, tp12058, tm12058, ep12058, em12058, dsL]
  · norm_num [world12058, agent12058, scalar12058, tp12058, tm12058, ep12058, em12058, dsL]
  · norm_num [world12058, agent12058, scalar12058, tp12058, tm12058, ep12058, em12058, dsL]
  · norm_num [world12058, agent12058, scalar12058, tp12058, tm12058, ep12058, em12058, dsL]
  · norm_num [world12058, agent12058, scalar12058, tp12058, tm12058, ep12058, em12058, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12058, agent12058, tp12058, tm12058, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12058, agent12058, tp12058, tm12058, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12058, agent12058, scalar12058, tp12058, tm12058, ep12058, em12058, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12058, agent12058, tp12058, tm12058, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12058, agent12058, scalar12058, tp12058, tm12058, ep12058, em12058, dsL]

theorem tails12058 :
    exp (-((12058:ℝ)*ep12058)) ≤ scalar12058.upperTail ∧
    exp (-((12058:ℝ)*em12058)) ≤ scalar12058.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12058:ℝ)) (by norm_num [ep12058]) ?_)
      (show bp12058^8 ≤ scalar12058.upperTail by norm_num [bp12058, scalar12058])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12058, bp12058, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12058:ℝ)) (by norm_num [em12058]) ?_)
      (show bm12058^8 ≤ scalar12058.lowerTail by norm_num [bm12058, scalar12058])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12058, bm12058, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12058 :
    agent12058.root+dsL+scalar12058.worldRadius < √(1/100/aL) ∧
    2*(agent12058.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12058, agent12058, scalar12058, tp12058, tm12058, ep12058, em12058, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12058, agent12058, scalar12058, tp12058, tm12058, ep12058, em12058, dsL]

noncomputable def master12058 : MasterCertificate 12058 world12058 agent12058 :=
  master scalar12058 dsL tp12058 tm12058 ep12058 em12058
    (by norm_num [dsL]) (by norm_num [tp12058]) (by norm_num [tm12058])
    (by norm_num [ep12058]) (by norm_num [em12058])
    positive12058 negative12058 tails12058.1 tails12058.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12058.1 tailGuards12058.2

theorem preserves12058 : master12058.toScalarCertificate = scalar12058 := rfl

end BstLean.Part281
