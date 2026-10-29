import BstLean.Part261Checker
import BstLean.Part268Scalar4
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12450 : ℝ := (2292234189 / 10000000000)
noncomputable def tm12450 : ℝ := (-((1502251353 / 2500000000)))
noncomputable def ep12450 : ℝ := (10139417797274557 / 20000000000000000000)
noncomputable def em12450 : ℝ := (24737463474320569 / 50000000000000000000)
noncomputable def bp12450 : ℝ := (22715546503723311367 / 50000000000000000000)
noncomputable def bm12450 : ℝ := (5787932193402955547 / 12500000000000000000)

theorem positive12450 :
    Eplus aL (agent12450.root+dsL) scalar12450.worldRadius world12450.frame
      agent12450.frame tp12450 ≤ -ep12450 := by
  apply positive_check (eT := (4620542920416073363 / 4000000000000000000)) (y := (18834981752960294137 / 50000000000000000000)) (u := (72873323589423985957 / 50000000000000000000))
  · norm_num [world12450, agent12450, scalar12450, tp12450, tm12450, ep12450, em12450, dsL]
  · norm_num [world12450, agent12450, scalar12450, tp12450, tm12450, ep12450, em12450, dsL]
  · norm_num [world12450, agent12450, scalar12450, tp12450, tm12450, ep12450, em12450, dsL]
  · norm_num [world12450, agent12450, scalar12450, tp12450, tm12450, ep12450, em12450, dsL]
  · norm_num [world12450, agent12450, scalar12450, tp12450, tm12450, ep12450, em12450, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12450, agent12450, tp12450, tm12450, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12450, agent12450, scalar12450, tp12450, tm12450, ep12450, em12450, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12450, agent12450, tp12450, tm12450, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12450, agent12450, scalar12450, tp12450, tm12450, ep12450, em12450, dsL]

theorem negative12450 :
    Eminus aL (agent12450.root+dsL) scalar12450.worldRadius world12450.frame
      agent12450.frame tm12450 ≤ -em12450 := by
  apply negative_check (lo := (13703765058303173991 / 20000000000000000000)) (hi := (17129706322878967489 / 25000000000000000000))
    (y := (-((71704796085006931371 / 100000000000000000000)))) (u := (9763825813484936589 / 20000000000000000000))
  · norm_num [world12450, agent12450, scalar12450, tp12450, tm12450, ep12450, em12450, dsL]
  · norm_num [world12450, agent12450, scalar12450, tp12450, tm12450, ep12450, em12450, dsL]
  · norm_num [world12450, agent12450, scalar12450, tp12450, tm12450, ep12450, em12450, dsL]
  · norm_num [world12450, agent12450, scalar12450, tp12450, tm12450, ep12450, em12450, dsL]
  · norm_num [world12450, agent12450, scalar12450, tp12450, tm12450, ep12450, em12450, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12450, agent12450, tp12450, tm12450, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12450, agent12450, tp12450, tm12450, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12450, agent12450, scalar12450, tp12450, tm12450, ep12450, em12450, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12450, agent12450, tp12450, tm12450, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12450, agent12450, scalar12450, tp12450, tm12450, ep12450, em12450, dsL]

theorem tails12450 :
    exp (-((12450:ℝ)*ep12450)) ≤ scalar12450.upperTail ∧
    exp (-((12450:ℝ)*em12450)) ≤ scalar12450.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12450:ℝ)) (by norm_num [ep12450]) ?_)
      (show bp12450^8 ≤ scalar12450.upperTail by norm_num [bp12450, scalar12450])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12450, bp12450, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12450:ℝ)) (by norm_num [em12450]) ?_)
      (show bm12450^8 ≤ scalar12450.lowerTail by norm_num [bm12450, scalar12450])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12450, bm12450, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12450 :
    agent12450.root+dsL+scalar12450.worldRadius < √(1/100/aL) ∧
    2*(agent12450.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12450, agent12450, scalar12450, tp12450, tm12450, ep12450, em12450, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12450, agent12450, scalar12450, tp12450, tm12450, ep12450, em12450, dsL]

noncomputable def master12450 : MasterCertificate 12450 world12450 agent12450 :=
  master scalar12450 dsL tp12450 tm12450 ep12450 em12450
    (by norm_num [dsL]) (by norm_num [tp12450]) (by norm_num [tm12450])
    (by norm_num [ep12450]) (by norm_num [em12450])
    positive12450 negative12450 tails12450.1 tails12450.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12450.1 tailGuards12450.2

theorem preserves12450 : master12450.toScalarCertificate = scalar12450 := rfl

noncomputable def tp12451 : ℝ := (1146164003 / 5000000000)
noncomputable def tm12451 : ℝ := (-((3004604219 / 5000000000)))
noncomputable def ep12451 : ℝ := (25350001808407711 / 50000000000000000000)
noncomputable def em12451 : ℝ := (12369361292833167 / 25000000000000000000)
noncomputable def bp12451 : ℝ := (22713076687113766539 / 50000000000000000000)
noncomputable def bm12451 : ℝ := (11574694859364531779 / 25000000000000000000)

theorem positive12451 :
    Eplus aL (agent12451.root+dsL) scalar12451.worldRadius world12451.frame
      agent12451.frame tp12451 ≤ -ep12451 := by
  apply positive_check (eT := (115513873117869849241 / 100000000000000000000)) (y := (37670847417704930627 / 100000000000000000000)) (u := (3643698386408281987 / 2500000000000000000))
  · norm_num [world12451, agent12451, scalar12451, tp12451, tm12451, ep12451, em12451, dsL]
  · norm_num [world12451, agent12451, scalar12451, tp12451, tm12451, ep12451, em12451, dsL]
  · norm_num [world12451, agent12451, scalar12451, tp12451, tm12451, ep12451, em12451, dsL]
  · norm_num [world12451, agent12451, scalar12451, tp12451, tm12451, ep12451, em12451, dsL]
  · norm_num [world12451, agent12451, scalar12451, tp12451, tm12451, ep12451, em12451, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12451, agent12451, tp12451, tm12451, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12451, agent12451, scalar12451, tp12451, tm12451, ep12451, em12451, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12451, agent12451, tp12451, tm12451, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12451, agent12451, scalar12451, tp12451, tm12451, ep12451, em12451, dsL]

theorem negative12451 :
    Eminus aL (agent12451.root+dsL) scalar12451.worldRadius world12451.frame
      agent12451.frame tm12451 ≤ -em12451 := by
  apply negative_check (lo := (68518543620984454253 / 100000000000000000000)) (hi := (34259271810492227127 / 50000000000000000000))
    (y := (-((1120390192553498531 / 1562500000000000000)))) (u := (9763808605888049947 / 20000000000000000000))
  · norm_num [world12451, agent12451, scalar12451, tp12451, tm12451, ep12451, em12451, dsL]
  · norm_num [world12451, agent12451, scalar12451, tp12451, tm12451, ep12451, em12451, dsL]
  · norm_num [world12451, agent12451, scalar12451, tp12451, tm12451, ep12451, em12451, dsL]
  · norm_num [world12451, agent12451, scalar12451, tp12451, tm12451, ep12451, em12451, dsL]
  · norm_num [world12451, agent12451, scalar12451, tp12451, tm12451, ep12451, em12451, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12451, agent12451, tp12451, tm12451, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12451, agent12451, tp12451, tm12451, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12451, agent12451, scalar12451, tp12451, tm12451, ep12451, em12451, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12451, agent12451, tp12451, tm12451, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12451, agent12451, scalar12451, tp12451, tm12451, ep12451, em12451, dsL]

theorem tails12451 :
    exp (-((12451:ℝ)*ep12451)) ≤ scalar12451.upperTail ∧
    exp (-((12451:ℝ)*em12451)) ≤ scalar12451.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12451:ℝ)) (by norm_num [ep12451]) ?_)
      (show bp12451^8 ≤ scalar12451.upperTail by norm_num [bp12451, scalar12451])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12451, bp12451, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12451:ℝ)) (by norm_num [em12451]) ?_)
      (show bm12451^8 ≤ scalar12451.lowerTail by norm_num [bm12451, scalar12451])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12451, bm12451, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12451 :
    agent12451.root+dsL+scalar12451.worldRadius < √(1/100/aL) ∧
    2*(agent12451.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12451, agent12451, scalar12451, tp12451, tm12451, ep12451, em12451, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12451, agent12451, scalar12451, tp12451, tm12451, ep12451, em12451, dsL]

noncomputable def master12451 : MasterCertificate 12451 world12451 agent12451 :=
  master scalar12451 dsL tp12451 tm12451 ep12451 em12451
    (by norm_num [dsL]) (by norm_num [tp12451]) (by norm_num [tm12451])
    (by norm_num [ep12451]) (by norm_num [em12451])
    positive12451 negative12451 tails12451.1 tails12451.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12451.1 tailGuards12451.2

theorem preserves12451 : master12451.toScalarCertificate = scalar12451 := rfl

noncomputable def tp12452 : ℝ := (2292421777 / 10000000000)
noncomputable def tm12452 : ℝ := (-((6009411413 / 10000000000)))
noncomputable def ep12452 : ℝ := (12675729301127579 / 25000000000000000000)
noncomputable def em12452 : ℝ := (24739981204942583 / 50000000000000000000)
noncomputable def bp12452 : ℝ := (363369717474583581 / 800000000000000000)
noncomputable def bm12452 : ℝ := (4629410221802090929 / 10000000000000000000)

theorem positive12452 :
    Eplus aL (agent12452.root+dsL) scalar12452.worldRadius world12452.frame
      agent12452.frame tp12452 ≤ -ep12452 := by
  apply positive_check (eT := (115514172923307645351 / 100000000000000000000)) (y := (18835865444394852967 / 50000000000000000000)) (u := (7287461155144283863 / 5000000000000000000))
  · norm_num [world12452, agent12452, scalar12452, tp12452, tm12452, ep12452, em12452, dsL]
  · norm_num [world12452, agent12452, scalar12452, tp12452, tm12452, ep12452, em12452, dsL]
  · norm_num [world12452, agent12452, scalar12452, tp12452, tm12452, ep12452, em12452, dsL]
  · norm_num [world12452, agent12452, scalar12452, tp12452, tm12452, ep12452, em12452, dsL]
  · norm_num [world12452, agent12452, scalar12452, tp12452, tm12452, ep12452, em12452, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12452, agent12452, tp12452, tm12452, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12452, agent12452, scalar12452, tp12452, tm12452, ep12452, em12452, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12452, agent12452, tp12452, tm12452, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12452, agent12452, scalar12452, tp12452, tm12452, ep12452, em12452, dsL]

theorem negative12452 :
    Eminus aL (agent12452.root+dsL) scalar12452.worldRadius world12452.frame
      agent12452.frame tm12452 ≤ -em12452 := by
  apply negative_check (lo := (68518262114018679879 / 100000000000000000000)) (hi := (1712956552850466997 / 2500000000000000000))
    (y := (-((2868205949126858227 / 4000000000000000000)))) (u := (48818956910406596531 / 100000000000000000000))
  · norm_num [world12452, agent12452, scalar12452, tp12452, tm12452, ep12452, em12452, dsL]
  · norm_num [world12452, agent12452, scalar12452, tp12452, tm12452, ep12452, em12452, dsL]
  · norm_num [world12452, agent12452, scalar12452, tp12452, tm12452, ep12452, em12452, dsL]
  · norm_num [world12452, agent12452, scalar12452, tp12452, tm12452, ep12452, em12452, dsL]
  · norm_num [world12452, agent12452, scalar12452, tp12452, tm12452, ep12452, em12452, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12452, agent12452, tp12452, tm12452, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12452, agent12452, tp12452, tm12452, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12452, agent12452, scalar12452, tp12452, tm12452, ep12452, em12452, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12452, agent12452, tp12452, tm12452, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12452, agent12452, scalar12452, tp12452, tm12452, ep12452, em12452, dsL]

theorem tails12452 :
    exp (-((12452:ℝ)*ep12452)) ≤ scalar12452.upperTail ∧
    exp (-((12452:ℝ)*em12452)) ≤ scalar12452.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12452:ℝ)) (by norm_num [ep12452]) ?_)
      (show bp12452^8 ≤ scalar12452.upperTail by norm_num [bp12452, scalar12452])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12452, bp12452, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12452:ℝ)) (by norm_num [em12452]) ?_)
      (show bm12452^8 ≤ scalar12452.lowerTail by norm_num [bm12452, scalar12452])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12452, bm12452, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12452 :
    agent12452.root+dsL+scalar12452.worldRadius < √(1/100/aL) ∧
    2*(agent12452.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12452, agent12452, scalar12452, tp12452, tm12452, ep12452, em12452, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12452, agent12452, scalar12452, tp12452, tm12452, ep12452, em12452, dsL]

noncomputable def master12452 : MasterCertificate 12452 world12452 agent12452 :=
  master scalar12452 dsL tp12452 tm12452 ep12452 em12452
    (by norm_num [dsL]) (by norm_num [tp12452]) (by norm_num [tm12452])
    (by norm_num [ep12452]) (by norm_num [em12452])
    positive12452 negative12452 tails12452.1 tails12452.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12452.1 tailGuards12452.2

theorem preserves12452 : master12452.toScalarCertificate = scalar12452 := rfl

noncomputable def tp12453 : ℝ := (573128877 / 2500000000)
noncomputable def tm12453 : ℝ := (-((3004807019 / 5000000000)))
noncomputable def ep12453 : ℝ := (25352914477039763 / 50000000000000000000)
noncomputable def em12453 : ℝ := (9896495591674347 / 20000000000000000000)
noncomputable def bp12453 : ℝ := (45416277500020849277 / 100000000000000000000)
noncomputable def bm12453 : ℝ := (361636143730984929 / 781250000000000000)

theorem positive12453 :
    Eplus aL (agent12453.root+dsL) scalar12453.worldRadius world12453.frame
      agent12453.frame tp12453 ≤ -ep12453 := by
  apply positive_check (eT := (57757236235173344291 / 50000000000000000000)) (y := (941815354361006411 / 2500000000000000000)) (u := (9109406905659048797 / 6250000000000000000))
  · norm_num [world12453, agent12453, scalar12453, tp12453, tm12453, ep12453, em12453, dsL]
  · norm_num [world12453, agent12453, scalar12453, tp12453, tm12453, ep12453, em12453, dsL]
  · norm_num [world12453, agent12453, scalar12453, tp12453, tm12453, ep12453, em12453, dsL]
  · norm_num [world12453, agent12453, scalar12453, tp12453, tm12453, ep12453, em12453, dsL]
  · norm_num [world12453, agent12453, scalar12453, tp12453, tm12453, ep12453, em12453, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12453, agent12453, tp12453, tm12453, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12453, agent12453, scalar12453, tp12453, tm12453, ep12453, em12453, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12453, agent12453, tp12453, tm12453, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12453, agent12453, scalar12453, tp12453, tm12453, ep12453, em12453, dsL]

theorem negative12453 :
    Eminus aL (agent12453.root+dsL) scalar12453.worldRadius world12453.frame
      agent12453.frame tm12453 ≤ -em12453 := by
  apply negative_check (lo := (68517982059452116299 / 100000000000000000000)) (hi := (685179820594521163 / 1000000000000000000))
    (y := (-((71705322645005496457 / 100000000000000000000)))) (u := (12204718001524039421 / 25000000000000000000))
  · norm_num [world12453, agent12453, scalar12453, tp12453, tm12453, ep12453, em12453, dsL]
  · norm_num [world12453, agent12453, scalar12453, tp12453, tm12453, ep12453, em12453, dsL]
  · norm_num [world12453, agent12453, scalar12453, tp12453, tm12453, ep12453, em12453, dsL]
  · norm_num [world12453, agent12453, scalar12453, tp12453, tm12453, ep12453, em12453, dsL]
  · norm_num [world12453, agent12453, scalar12453, tp12453, tm12453, ep12453, em12453, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12453, agent12453, tp12453, tm12453, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12453, agent12453, tp12453, tm12453, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12453, agent12453, scalar12453, tp12453, tm12453, ep12453, em12453, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12453, agent12453, tp12453, tm12453, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12453, agent12453, scalar12453, tp12453, tm12453, ep12453, em12453, dsL]

theorem tails12453 :
    exp (-((12453:ℝ)*ep12453)) ≤ scalar12453.upperTail ∧
    exp (-((12453:ℝ)*em12453)) ≤ scalar12453.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12453:ℝ)) (by norm_num [ep12453]) ?_)
      (show bp12453^8 ≤ scalar12453.upperTail by norm_num [bp12453, scalar12453])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12453, bp12453, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12453:ℝ)) (by norm_num [em12453]) ?_)
      (show bm12453^8 ≤ scalar12453.lowerTail by norm_num [bm12453, scalar12453])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12453, bm12453, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12453 :
    agent12453.root+dsL+scalar12453.worldRadius < √(1/100/aL) ∧
    2*(agent12453.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12453, agent12453, scalar12453, tp12453, tm12453, ep12453, em12453, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12453, agent12453, scalar12453, tp12453, tm12453, ep12453, em12453, dsL]

noncomputable def master12453 : MasterCertificate 12453 world12453 agent12453 :=
  master scalar12453 dsL tp12453 tm12453 ep12453 em12453
    (by norm_num [dsL]) (by norm_num [tp12453]) (by norm_num [tm12453])
    (by norm_num [ep12453]) (by norm_num [em12453])
    positive12453 negative12453 tails12453.1 tails12453.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12453.1 tailGuards12453.2

theorem preserves12453 : master12453.toScalarCertificate = scalar12453 := rfl

noncomputable def tp12454 : ℝ := (2292609253 / 10000000000)
noncomputable def tm12454 : ℝ := (-((3004908371 / 5000000000)))
noncomputable def ep12454 : ℝ := (50708739520615831 / 100000000000000000000)
noncomputable def em12454 : ℝ := (49484992376079547 / 100000000000000000000)
noncomputable def bp12454 : ℝ := (9082268271629604247 / 20000000000000000000)
noncomputable def bm12454 : ℝ := (1851390062922836009 / 4000000000000000000)

theorem positive12454 :
    Eplus aL (agent12454.root+dsL) scalar12454.worldRadius world12454.frame
      agent12454.frame tp12454 ≤ -ep12454 := by
  apply positive_check (eT := (4620590886056260353 / 4000000000000000000)) (y := (9418374557284916481 / 25000000000000000000)) (u := (29150359802095557569 / 20000000000000000000))
  · norm_num [world12454, agent12454, scalar12454, tp12454, tm12454, ep12454, em12454, dsL]
  · norm_num [world12454, agent12454, scalar12454, tp12454, tm12454, ep12454, em12454, dsL]
  · norm_num [world12454, agent12454, scalar12454, tp12454, tm12454, ep12454, em12454, dsL]
  · norm_num [world12454, agent12454, scalar12454, tp12454, tm12454, ep12454, em12454, dsL]
  · norm_num [world12454, agent12454, scalar12454, tp12454, tm12454, ep12454, em12454, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12454, agent12454, tp12454, tm12454, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12454, agent12454, scalar12454, tp12454, tm12454, ep12454, em12454, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12454, agent12454, tp12454, tm12454, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12454, agent12454, scalar12454, tp12454, tm12454, ep12454, em12454, dsL]

theorem negative12454 :
    Eminus aL (agent12454.root+dsL) scalar12454.worldRadius world12454.frame
      agent12454.frame tm12454 ≤ -em12454 := by
  apply negative_check (lo := (68517701608009745969 / 100000000000000000000)) (hi := (6851770160800974597 / 10000000000000000000))
    (y := (-((7170549829189989823 / 10000000000000000000)))) (u := (6102348282167363067 / 12500000000000000000))
  · norm_num [world12454, agent12454, scalar12454, tp12454, tm12454, ep12454, em12454, dsL]
  · norm_num [world12454, agent12454, scalar12454, tp12454, tm12454, ep12454, em12454, dsL]
  · norm_num [world12454, agent12454, scalar12454, tp12454, tm12454, ep12454, em12454, dsL]
  · norm_num [world12454, agent12454, scalar12454, tp12454, tm12454, ep12454, em12454, dsL]
  · norm_num [world12454, agent12454, scalar12454, tp12454, tm12454, ep12454, em12454, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12454, agent12454, tp12454, tm12454, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12454, agent12454, tp12454, tm12454, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12454, agent12454, scalar12454, tp12454, tm12454, ep12454, em12454, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12454, agent12454, tp12454, tm12454, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12454, agent12454, scalar12454, tp12454, tm12454, ep12454, em12454, dsL]

theorem tails12454 :
    exp (-((12454:ℝ)*ep12454)) ≤ scalar12454.upperTail ∧
    exp (-((12454:ℝ)*em12454)) ≤ scalar12454.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12454:ℝ)) (by norm_num [ep12454]) ?_)
      (show bp12454^8 ≤ scalar12454.upperTail by norm_num [bp12454, scalar12454])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12454, bp12454, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12454:ℝ)) (by norm_num [em12454]) ?_)
      (show bm12454^8 ≤ scalar12454.lowerTail by norm_num [bm12454, scalar12454])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12454, bm12454, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12454 :
    agent12454.root+dsL+scalar12454.worldRadius < √(1/100/aL) ∧
    2*(agent12454.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12454, agent12454, scalar12454, tp12454, tm12454, ep12454, em12454, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12454, agent12454, scalar12454, tp12454, tm12454, ep12454, em12454, dsL]

noncomputable def master12454 : MasterCertificate 12454 world12454 agent12454 :=
  master scalar12454 dsL tp12454 tm12454 ep12454 em12454
    (by norm_num [dsL]) (by norm_num [tp12454]) (by norm_num [tm12454])
    (by norm_num [ep12454]) (by norm_num [em12454])
    positive12454 negative12454 tails12454.1 tails12454.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12454.1 tailGuards12454.2

theorem preserves12454 : master12454.toScalarCertificate = scalar12454 := rfl

noncomputable def tp12455 : ℝ := (2292702969 / 10000000000)
noncomputable def tm12455 : ℝ := (-((6010019537 / 10000000000)))
noncomputable def ep12455 : ℝ := (6338956219788517 / 12500000000000000000)
noncomputable def em12455 : ℝ := (12371876684279881 / 25000000000000000000)
noncomputable def bp12455 : ℝ := (45406405654838598493 / 100000000000000000000)
noncomputable def bm12455 : ℝ := (4628007697060370471 / 10000000000000000000)

theorem positive12455 :
    Eplus aL (agent12455.root+dsL) scalar12455.worldRadius world12455.frame
      agent12455.frame tp12455 ≤ -ep12455 := by
  apply positive_check (eT := (57757535826992915929 / 50000000000000000000)) (y := (1883719011021419673 / 5000000000000000000)) (u := (36438271133579329933 / 25000000000000000000))
  · norm_num [world12455, agent12455, scalar12455, tp12455, tm12455, ep12455, em12455, dsL]
  · norm_num [world12455, agent12455, scalar12455, tp12455, tm12455, ep12455, em12455, dsL]
  · norm_num [world12455, agent12455, scalar12455, tp12455, tm12455, ep12455, em12455, dsL]
  · norm_num [world12455, agent12455, scalar12455, tp12455, tm12455, ep12455, em12455, dsL]
  · norm_num [world12455, agent12455, scalar12455, tp12455, tm12455, ep12455, em12455, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12455, agent12455, tp12455, tm12455, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12455, agent12455, scalar12455, tp12455, tm12455, ep12455, em12455, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12455, agent12455, tp12455, tm12455, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12455, agent12455, scalar12455, tp12455, tm12455, ep12455, em12455, dsL]

theorem negative12455 :
    Eminus aL (agent12455.root+dsL) scalar12455.worldRadius world12455.frame
      agent12455.frame tm12455 ≤ -em12455 := by
  apply negative_check (lo := (34258710354013554297 / 50000000000000000000)) (hi := (13703484141605421719 / 20000000000000000000))
    (y := (-((35852835807911709341 / 50000000000000000000)))) (u := (24409350821388238457 / 50000000000000000000))
  · norm_num [world12455, agent12455, scalar12455, tp12455, tm12455, ep12455, em12455, dsL]
  · norm_num [world12455, agent12455, scalar12455, tp12455, tm12455, ep12455, em12455, dsL]
  · norm_num [world12455, agent12455, scalar12455, tp12455, tm12455, ep12455, em12455, dsL]
  · norm_num [world12455, agent12455, scalar12455, tp12455, tm12455, ep12455, em12455, dsL]
  · norm_num [world12455, agent12455, scalar12455, tp12455, tm12455, ep12455, em12455, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12455, agent12455, tp12455, tm12455, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12455, agent12455, tp12455, tm12455, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12455, agent12455, scalar12455, tp12455, tm12455, ep12455, em12455, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12455, agent12455, tp12455, tm12455, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12455, agent12455, scalar12455, tp12455, tm12455, ep12455, em12455, dsL]

theorem tails12455 :
    exp (-((12455:ℝ)*ep12455)) ≤ scalar12455.upperTail ∧
    exp (-((12455:ℝ)*em12455)) ≤ scalar12455.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12455:ℝ)) (by norm_num [ep12455]) ?_)
      (show bp12455^8 ≤ scalar12455.upperTail by norm_num [bp12455, scalar12455])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12455, bp12455, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12455:ℝ)) (by norm_num [em12455]) ?_)
      (show bm12455^8 ≤ scalar12455.lowerTail by norm_num [bm12455, scalar12455])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12455, bm12455, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12455 :
    agent12455.root+dsL+scalar12455.worldRadius < √(1/100/aL) ∧
    2*(agent12455.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12455, agent12455, scalar12455, tp12455, tm12455, ep12455, em12455, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12455, agent12455, scalar12455, tp12455, tm12455, ep12455, em12455, dsL]

noncomputable def master12455 : MasterCertificate 12455 world12455 agent12455 :=
  master scalar12455 dsL tp12455 tm12455 ep12455 em12455
    (by norm_num [dsL]) (by norm_num [tp12455]) (by norm_num [tm12455])
    (by norm_num [ep12455]) (by norm_num [em12455])
    positive12455 negative12455 tails12455.1 tails12455.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12455.1 tailGuards12455.2

theorem preserves12455 : master12455.toScalarCertificate = scalar12455 := rfl

noncomputable def tp12456 : ℝ := (2292796859 / 10000000000)
noncomputable def tm12456 : ℝ := (-((6010222787 / 10000000000)))
noncomputable def ep12456 : ℝ := (50714563126228061 / 100000000000000000000)
noncomputable def em12456 : ℝ := (989800494223787 / 2000000000000000000)
noncomputable def bp12456 : ℝ := (9080293588980287149 / 20000000000000000000)
noncomputable def bm12456 : ℝ := (11568849986538970511 / 25000000000000000000)

theorem positive12456 :
    Eplus aL (agent12456.root+dsL) scalar12456.worldRadius world12456.frame
      agent12456.frame tp12456 ≤ -ep12456 := by
  apply positive_check (eT := (23103074490651077693 / 20000000000000000000)) (y := (37675259436161367577 / 100000000000000000000)) (u := (72877183012000680859 / 50000000000000000000))
  · norm_num [world12456, agent12456, scalar12456, tp12456, tm12456, ep12456, em12456, dsL]
  · norm_num [world12456, agent12456, scalar12456, tp12456, tm12456, ep12456, em12456, dsL]
  · norm_num [world12456, agent12456, scalar12456, tp12456, tm12456, ep12456, em12456, dsL]
  · norm_num [world12456, agent12456, scalar12456, tp12456, tm12456, ep12456, em12456, dsL]
  · norm_num [world12456, agent12456, scalar12456, tp12456, tm12456, ep12456, em12456, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12456, agent12456, tp12456, tm12456, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12456, agent12456, scalar12456, tp12456, tm12456, ep12456, em12456, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12456, agent12456, tp12456, tm12456, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12456, agent12456, scalar12456, tp12456, tm12456, ep12456, em12456, dsL]

theorem negative12456 :
    Eminus aL (agent12456.root+dsL) scalar12456.worldRadius world12456.frame
      agent12456.frame tm12456 ≤ -em12456 := by
  apply negative_check (lo := (68517137790606249553 / 100000000000000000000)) (hi := (34258568895303124777 / 50000000000000000000))
    (y := (-((14341167515333328359 / 20000000000000000000)))) (u := (12204655155728702657 / 25000000000000000000))
  · norm_num [world12456, agent12456, scalar12456, tp12456, tm12456, ep12456, em12456, dsL]
  · norm_num [world12456, agent12456, scalar12456, tp12456, tm12456, ep12456, em12456, dsL]
  · norm_num [world12456, agent12456, scalar12456, tp12456, tm12456, ep12456, em12456, dsL]
  · norm_num [world12456, agent12456, scalar12456, tp12456, tm12456, ep12456, em12456, dsL]
  · norm_num [world12456, agent12456, scalar12456, tp12456, tm12456, ep12456, em12456, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12456, agent12456, tp12456, tm12456, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12456, agent12456, tp12456, tm12456, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12456, agent12456, scalar12456, tp12456, tm12456, ep12456, em12456, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12456, agent12456, tp12456, tm12456, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12456, agent12456, scalar12456, tp12456, tm12456, ep12456, em12456, dsL]

theorem tails12456 :
    exp (-((12456:ℝ)*ep12456)) ≤ scalar12456.upperTail ∧
    exp (-((12456:ℝ)*em12456)) ≤ scalar12456.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12456:ℝ)) (by norm_num [ep12456]) ?_)
      (show bp12456^8 ≤ scalar12456.upperTail by norm_num [bp12456, scalar12456])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12456, bp12456, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12456:ℝ)) (by norm_num [em12456]) ?_)
      (show bm12456^8 ≤ scalar12456.lowerTail by norm_num [bm12456, scalar12456])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12456, bm12456, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12456 :
    agent12456.root+dsL+scalar12456.worldRadius < √(1/100/aL) ∧
    2*(agent12456.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12456, agent12456, scalar12456, tp12456, tm12456, ep12456, em12456, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12456, agent12456, scalar12456, tp12456, tm12456, ep12456, em12456, dsL]

noncomputable def master12456 : MasterCertificate 12456 world12456 agent12456 :=
  master scalar12456 dsL tp12456 tm12456 ep12456 em12456
    (by norm_num [dsL]) (by norm_num [tp12456]) (by norm_num [tm12456])
    (by norm_num [ep12456]) (by norm_num [em12456])
    positive12456 negative12456 tails12456.1 tails12456.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12456.1 tailGuards12456.2

theorem preserves12456 : master12456.toScalarCertificate = scalar12456 := rfl

noncomputable def tp12457 : ℝ := (1146445373 / 5000000000)
noncomputable def tm12457 : ℝ := (-((1202085219 / 2000000000)))
noncomputable def ep12457 : ℝ := (2028698993802973 / 4000000000000000000)
noncomputable def em12457 : ℝ := (12373135280917341 / 25000000000000000000)
noncomputable def bp12457 : ℝ := (45396531606970900753 / 100000000000000000000)
noncomputable def bm12457 : ℝ := (9254144845641485751 / 20000000000000000000)

theorem positive12457 :
    Eplus aL (agent12457.root+dsL) scalar12457.worldRadius world12457.frame
      agent12457.frame tp12457 ≤ -ep12457 := by
  apply positive_check (eT := (115515673262931250987 / 100000000000000000000)) (y := (37676139168653740667 / 100000000000000000000)) (u := (7287782413907926111 / 5000000000000000000))
  · norm_num [world12457, agent12457, scalar12457, tp12457, tm12457, ep12457, em12457, dsL]
  · norm_num [world12457, agent12457, scalar12457, tp12457, tm12457, ep12457, em12457, dsL]
  · norm_num [world12457, agent12457, scalar12457, tp12457, tm12457, ep12457, em12457, dsL]
  · norm_num [world12457, agent12457, scalar12457, tp12457, tm12457, ep12457, em12457, dsL]
  · norm_num [world12457, agent12457, scalar12457, tp12457, tm12457, ep12457, em12457, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12457, agent12457, tp12457, tm12457, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12457, agent12457, scalar12457, tp12457, tm12457, ep12457, em12457, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12457, agent12457, tp12457, tm12457, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12457, agent12457, scalar12457, tp12457, tm12457, ep12457, em12457, dsL]

theorem negative12457 :
    Eminus aL (agent12457.root+dsL) scalar12457.worldRadius world12457.frame
      agent12457.frame tm12457 ≤ -em12457 := by
  apply negative_check (lo := (68516854567049751241 / 100000000000000000000)) (hi := (34258427283524875621 / 50000000000000000000))
    (y := (-((717060049313734657 / 1000000000000000000)))) (u := (48818538922723756251 / 100000000000000000000))
  · norm_num [world12457, agent12457, scalar12457, tp12457, tm12457, ep12457, em12457, dsL]
  · norm_num [world12457, agent12457, scalar12457, tp12457, tm12457, ep12457, em12457, dsL]
  · norm_num [world12457, agent12457, scalar12457, tp12457, tm12457, ep12457, em12457, dsL]
  · norm_num [world12457, agent12457, scalar12457, tp12457, tm12457, ep12457, em12457, dsL]
  · norm_num [world12457, agent12457, scalar12457, tp12457, tm12457, ep12457, em12457, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12457, agent12457, tp12457, tm12457, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12457, agent12457, tp12457, tm12457, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12457, agent12457, scalar12457, tp12457, tm12457, ep12457, em12457, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12457, agent12457, tp12457, tm12457, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12457, agent12457, scalar12457, tp12457, tm12457, ep12457, em12457, dsL]

theorem tails12457 :
    exp (-((12457:ℝ)*ep12457)) ≤ scalar12457.upperTail ∧
    exp (-((12457:ℝ)*em12457)) ≤ scalar12457.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12457:ℝ)) (by norm_num [ep12457]) ?_)
      (show bp12457^8 ≤ scalar12457.upperTail by norm_num [bp12457, scalar12457])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12457, bp12457, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12457:ℝ)) (by norm_num [em12457]) ?_)
      (show bm12457^8 ≤ scalar12457.lowerTail by norm_num [bm12457, scalar12457])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12457, bm12457, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12457 :
    agent12457.root+dsL+scalar12457.worldRadius < √(1/100/aL) ∧
    2*(agent12457.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12457, agent12457, scalar12457, tp12457, tm12457, ep12457, em12457, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12457, agent12457, scalar12457, tp12457, tm12457, ep12457, em12457, dsL]

noncomputable def master12457 : MasterCertificate 12457 world12457 agent12457 :=
  master scalar12457 dsL tp12457 tm12457 ep12457 em12457
    (by norm_num [dsL]) (by norm_num [tp12457]) (by norm_num [tm12457])
    (by norm_num [ep12457]) (by norm_num [em12457])
    positive12457 negative12457 tails12457.1 tails12457.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12457.1 tailGuards12457.2

theorem preserves12457 : master12457.toScalarCertificate = scalar12457 := rfl

noncomputable def tp12458 : ℝ := (2292984507 / 10000000000)
noncomputable def tm12458 : ℝ := (-((3005314587 / 5000000000)))
noncomputable def ep12458 : ℝ := (10144077068623093 / 20000000000000000000)
noncomputable def em12458 : ℝ := (49495056433582101 / 100000000000000000000)
noncomputable def bp12458 : ℝ := (45391596338270757197 / 100000000000000000000)
noncomputable def bm12458 : ℝ := (5783256185751636099 / 12500000000000000000)

theorem positive12458 :
    Eplus aL (agent12458.root+dsL) scalar12458.worldRadius world12458.frame
      agent12458.frame tp12458 ≤ -ep12458 := by
  apply positive_check (eT := (115515973189248882899 / 100000000000000000000)) (y := (37677016996616538841 / 100000000000000000000)) (u := (145756927767612315537 / 100000000000000000000))
  · norm_num [world12458, agent12458, scalar12458, tp12458, tm12458, ep12458, em12458, dsL]
  · norm_num [world12458, agent12458, scalar12458, tp12458, tm12458, ep12458, em12458, dsL]
  · norm_num [world12458, agent12458, scalar12458, tp12458, tm12458, ep12458, em12458, dsL]
  · norm_num [world12458, agent12458, scalar12458, tp12458, tm12458, ep12458, em12458, dsL]
  · norm_num [world12458, agent12458, scalar12458, tp12458, tm12458, ep12458, em12458, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12458, agent12458, tp12458, tm12458, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12458, agent12458, scalar12458, tp12458, tm12458, ep12458, em12458, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12458, agent12458, tp12458, tm12458, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12458, agent12458, scalar12458, tp12458, tm12458, ep12458, em12458, dsL]

theorem negative12458 :
    Eminus aL (agent12458.root+dsL) scalar12458.worldRadius world12458.frame
      agent12458.frame tm12458 ≤ -em12458 := by
  apply negative_check (lo := (68516572274335351031 / 100000000000000000000)) (hi := (8564571534291918879 / 12500000000000000000))
    (y := (-((71706170824010872121 / 100000000000000000000)))) (u := (48818457936429169233 / 100000000000000000000))
  · norm_num [world12458, agent12458, scalar12458, tp12458, tm12458, ep12458, em12458, dsL]
  · norm_num [world12458, agent12458, scalar12458, tp12458, tm12458, ep12458, em12458, dsL]
  · norm_num [world12458, agent12458, scalar12458, tp12458, tm12458, ep12458, em12458, dsL]
  · norm_num [world12458, agent12458, scalar12458, tp12458, tm12458, ep12458, em12458, dsL]
  · norm_num [world12458, agent12458, scalar12458, tp12458, tm12458, ep12458, em12458, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12458, agent12458, tp12458, tm12458, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12458, agent12458, tp12458, tm12458, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12458, agent12458, scalar12458, tp12458, tm12458, ep12458, em12458, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12458, agent12458, tp12458, tm12458, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12458, agent12458, scalar12458, tp12458, tm12458, ep12458, em12458, dsL]

theorem tails12458 :
    exp (-((12458:ℝ)*ep12458)) ≤ scalar12458.upperTail ∧
    exp (-((12458:ℝ)*em12458)) ≤ scalar12458.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12458:ℝ)) (by norm_num [ep12458]) ?_)
      (show bp12458^8 ≤ scalar12458.upperTail by norm_num [bp12458, scalar12458])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12458, bp12458, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12458:ℝ)) (by norm_num [em12458]) ?_)
      (show bm12458^8 ≤ scalar12458.lowerTail by norm_num [bm12458, scalar12458])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12458, bm12458, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12458 :
    agent12458.root+dsL+scalar12458.worldRadius < √(1/100/aL) ∧
    2*(agent12458.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12458, agent12458, scalar12458, tp12458, tm12458, ep12458, em12458, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12458, agent12458, scalar12458, tp12458, tm12458, ep12458, em12458, dsL]

noncomputable def master12458 : MasterCertificate 12458 world12458 agent12458 :=
  master scalar12458 dsL tp12458 tm12458 ep12458 em12458
    (by norm_num [dsL]) (by norm_num [tp12458]) (by norm_num [tm12458])
    (by norm_num [ep12458]) (by norm_num [em12458])
    positive12458 negative12458 tails12458.1 tails12458.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12458.1 tailGuards12458.2

theorem preserves12458 : master12458.toScalarCertificate = scalar12458 := rfl

noncomputable def tp12459 : ℝ := (286634787 / 1250000000)
noncomputable def tm12459 : ℝ := (-((187838507 / 312500000)))
noncomputable def ep12459 : ℝ := (50723293730044249 / 100000000000000000000)
noncomputable def em12459 : ℝ := (49497569754417487 / 100000000000000000000)
noncomputable def bp12459 : ℝ := (22693331384040996451 / 50000000000000000000)
noncomputable def bm12459 : ℝ := (72283400559783829 / 156250000000000000)

theorem positive12459 :
    Eplus aL (agent12459.root+dsL) scalar12459.worldRadius world12459.frame
      agent12459.frame tp12459 ≤ -ep12459 := by
  apply positive_check (eT := (115516273351230145341 / 100000000000000000000)) (y := (37677895936551657333 / 100000000000000000000)) (u := (72879104444544401393 / 50000000000000000000))
  · norm_num [world12459, agent12459, scalar12459, tp12459, tm12459, ep12459, em12459, dsL]
  · norm_num [world12459, agent12459, scalar12459, tp12459, tm12459, ep12459, em12459, dsL]
  · norm_num [world12459, agent12459, scalar12459, tp12459, tm12459, ep12459, em12459, dsL]
  · norm_num [world12459, agent12459, scalar12459, tp12459, tm12459, ep12459, em12459, dsL]
  · norm_num [world12459, agent12459, scalar12459, tp12459, tm12459, ep12459, em12459, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12459, agent12459, tp12459, tm12459, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12459, agent12459, scalar12459, tp12459, tm12459, ep12459, em12459, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12459, agent12459, tp12459, tm12459, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12459, agent12459, scalar12459, tp12459, tm12459, ep12459, em12459, dsL]

theorem negative12459 :
    Eminus aL (agent12459.root+dsL) scalar12459.worldRadius world12459.frame
      agent12459.frame tm12459 ≤ -em12459 := by
  apply negative_check (lo := (3425814502524093383 / 5000000000000000000)) (hi := (68516290050481867661 / 100000000000000000000))
    (y := (-((17926584281791348657 / 25000000000000000000)))) (u := (24409188374930569819 / 50000000000000000000))
  · norm_num [world12459, agent12459, scalar12459, tp12459, tm12459, ep12459, em12459, dsL]
  · norm_num [world12459, agent12459, scalar12459, tp12459, tm12459, ep12459, em12459, dsL]
  · norm_num [world12459, agent12459, scalar12459, tp12459, tm12459, ep12459, em12459, dsL]
  · norm_num [world12459, agent12459, scalar12459, tp12459, tm12459, ep12459, em12459, dsL]
  · norm_num [world12459, agent12459, scalar12459, tp12459, tm12459, ep12459, em12459, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12459, agent12459, tp12459, tm12459, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12459, agent12459, tp12459, tm12459, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12459, agent12459, scalar12459, tp12459, tm12459, ep12459, em12459, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12459, agent12459, tp12459, tm12459, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12459, agent12459, scalar12459, tp12459, tm12459, ep12459, em12459, dsL]

theorem tails12459 :
    exp (-((12459:ℝ)*ep12459)) ≤ scalar12459.upperTail ∧
    exp (-((12459:ℝ)*em12459)) ≤ scalar12459.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12459:ℝ)) (by norm_num [ep12459]) ?_)
      (show bp12459^8 ≤ scalar12459.upperTail by norm_num [bp12459, scalar12459])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12459, bp12459, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12459:ℝ)) (by norm_num [em12459]) ?_)
      (show bm12459^8 ≤ scalar12459.lowerTail by norm_num [bm12459, scalar12459])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12459, bm12459, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12459 :
    agent12459.root+dsL+scalar12459.worldRadius < √(1/100/aL) ∧
    2*(agent12459.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12459, agent12459, scalar12459, tp12459, tm12459, ep12459, em12459, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12459, agent12459, scalar12459, tp12459, tm12459, ep12459, em12459, dsL]

noncomputable def master12459 : MasterCertificate 12459 world12459 agent12459 :=
  master scalar12459 dsL tp12459 tm12459 ep12459 em12459
    (by norm_num [dsL]) (by norm_num [tp12459]) (by norm_num [tm12459])
    (by norm_num [ep12459]) (by norm_num [em12459])
    positive12459 negative12459 tails12459.1 tails12459.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12459.1 tailGuards12459.2

theorem preserves12459 : master12459.toScalarCertificate = scalar12459 := rfl

noncomputable def tp12460 : ℝ := (2293248537 / 10000000000)
noncomputable def tm12460 : ℝ := (-((1202253221 / 2000000000)))
noncomputable def ep12460 : ℝ := (2536383713367753 / 5000000000000000000)
noncomputable def em12460 : ℝ := (24750842214894531 / 50000000000000000000)
noncomputable def bp12460 : ℝ := (45380688870104302343 / 100000000000000000000)
noncomputable def bm12460 : ℝ := (46255549733342147449 / 100000000000000000000)

theorem positive12460 :
    Eplus aL (agent12460.root+dsL) scalar12460.worldRadius world12460.frame
      agent12460.frame tp12460 ≤ -ep12460 := by
  apply positive_check (eT := (115517129059159310827 / 100000000000000000000)) (y := (37678041404338194287 / 100000000000000000000)) (u := (9109901307530199269 / 6250000000000000000))
  · norm_num [world12460, agent12460, scalar12460, tp12460, tm12460, ep12460, em12460, dsL]
  · norm_num [world12460, agent12460, scalar12460, tp12460, tm12460, ep12460, em12460, dsL]
  · norm_num [world12460, agent12460, scalar12460, tp12460, tm12460, ep12460, em12460, dsL]
  · norm_num [world12460, agent12460, scalar12460, tp12460, tm12460, ep12460, em12460, dsL]
  · norm_num [world12460, agent12460, scalar12460, tp12460, tm12460, ep12460, em12460, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12460, agent12460, tp12460, tm12460, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12460, agent12460, scalar12460, tp12460, tm12460, ep12460, em12460, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12460, agent12460, tp12460, tm12460, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12460, agent12460, scalar12460, tp12460, tm12460, ep12460, em12460, dsL]

theorem negative12460 :
    Eminus aL (agent12460.root+dsL) scalar12460.worldRadius world12460.frame
      agent12460.frame tm12460 ≤ -em12460 := by
  apply negative_check (lo := (3425750647623780321 / 5000000000000000000)) (hi := (68515012952475606421 / 100000000000000000000))
    (y := (-((896307073395291349 / 1250000000000000000)))) (u := (9763848291144586193 / 20000000000000000000))
  · norm_num [world12460, agent12460, scalar12460, tp12460, tm12460, ep12460, em12460, dsL]
  · norm_num [world12460, agent12460, scalar12460, tp12460, tm12460, ep12460, em12460, dsL]
  · norm_num [world12460, agent12460, scalar12460, tp12460, tm12460, ep12460, em12460, dsL]
  · norm_num [world12460, agent12460, scalar12460, tp12460, tm12460, ep12460, em12460, dsL]
  · norm_num [world12460, agent12460, scalar12460, tp12460, tm12460, ep12460, em12460, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12460, agent12460, tp12460, tm12460, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12460, agent12460, tp12460, tm12460, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12460, agent12460, scalar12460, tp12460, tm12460, ep12460, em12460, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12460, agent12460, tp12460, tm12460, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12460, agent12460, scalar12460, tp12460, tm12460, ep12460, em12460, dsL]

theorem tails12460 :
    exp (-((12460:ℝ)*ep12460)) ≤ scalar12460.upperTail ∧
    exp (-((12460:ℝ)*em12460)) ≤ scalar12460.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12460:ℝ)) (by norm_num [ep12460]) ?_)
      (show bp12460^8 ≤ scalar12460.upperTail by norm_num [bp12460, scalar12460])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12460, bp12460, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12460:ℝ)) (by norm_num [em12460]) ?_)
      (show bm12460^8 ≤ scalar12460.lowerTail by norm_num [bm12460, scalar12460])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12460, bm12460, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12460 :
    agent12460.root+dsL+scalar12460.worldRadius < √(1/100/aL) ∧
    2*(agent12460.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12460, agent12460, scalar12460, tp12460, tm12460, ep12460, em12460, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12460, agent12460, scalar12460, tp12460, tm12460, ep12460, em12460, dsL]

noncomputable def master12460 : MasterCertificate 12460 world12460 agent12460 :=
  master scalar12460 dsL tp12460 tm12460 ep12460 em12460
    (by norm_num [dsL]) (by norm_num [tp12460]) (by norm_num [tm12460])
    (by norm_num [ep12460]) (by norm_num [em12460])
    positive12460 negative12460 tails12460.1 tails12460.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12460.1 tailGuards12460.2

theorem preserves12460 : master12460.toScalarCertificate = scalar12460 := rfl

noncomputable def tp12461 : ℝ := (2293342227 / 10000000000)
noncomputable def tm12461 : ℝ := (-((1202293793 / 2000000000)))
noncomputable def ep12461 : ℝ := (12682644974771469 / 25000000000000000000)
noncomputable def em12461 : ℝ := (24752097599316739 / 50000000000000000000)
noncomputable def bp12461 : ℝ := (5671969711177132489 / 12500000000000000000)
noncomputable def bm12461 : ℝ := (11562719707705160873 / 25000000000000000000)

theorem positive12461 :
    Eplus aL (agent12461.root+dsL) scalar12461.worldRadius world12461.frame
      agent12461.frame tp12461 ≤ -ep12461 := by
  apply positive_check (eT := (2887935713873918917 / 2500000000000000000)) (y := (7535783877986377059 / 20000000000000000000)) (u := (145759700664038435451 / 100000000000000000000))
  · norm_num [world12461, agent12461, scalar12461, tp12461, tm12461, ep12461, em12461, dsL]
  · norm_num [world12461, agent12461, scalar12461, tp12461, tm12461, ep12461, em12461, dsL]
  · norm_num [world12461, agent12461, scalar12461, tp12461, tm12461, ep12461, em12461, dsL]
  · norm_num [world12461, agent12461, scalar12461, tp12461, tm12461, ep12461, em12461, dsL]
  · norm_num [world12461, agent12461, scalar12461, tp12461, tm12461, ep12461, em12461, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12461, agent12461, tp12461, tm12461, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12461, agent12461, scalar12461, tp12461, tm12461, ep12461, em12461, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12461, agent12461, tp12461, tm12461, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12461, agent12461, scalar12461, tp12461, tm12461, ep12461, em12461, dsL]

theorem negative12461 :
    Eminus aL (agent12461.root+dsL) scalar12461.worldRadius world12461.frame
      agent12461.frame tm12461 ≤ -em12461 := by
  apply negative_check (lo := (68514731462010808523 / 100000000000000000000)) (hi := (17128682865502702131 / 25000000000000000000))
    (y := (-((3585236589302264643 / 5000000000000000000)))) (u := (48819160457627846049 / 100000000000000000000))
  · norm_num [world12461, agent12461, scalar12461, tp12461, tm12461, ep12461, em12461, dsL]
  · norm_num [world12461, agent12461, scalar12461, tp12461, tm12461, ep12461, em12461, dsL]
  · norm_num [world12461, agent12461, scalar12461, tp12461, tm12461, ep12461, em12461, dsL]
  · norm_num [world12461, agent12461, scalar12461, tp12461, tm12461, ep12461, em12461, dsL]
  · norm_num [world12461, agent12461, scalar12461, tp12461, tm12461, ep12461, em12461, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12461, agent12461, tp12461, tm12461, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12461, agent12461, tp12461, tm12461, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12461, agent12461, scalar12461, tp12461, tm12461, ep12461, em12461, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12461, agent12461, tp12461, tm12461, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12461, agent12461, scalar12461, tp12461, tm12461, ep12461, em12461, dsL]

theorem tails12461 :
    exp (-((12461:ℝ)*ep12461)) ≤ scalar12461.upperTail ∧
    exp (-((12461:ℝ)*em12461)) ≤ scalar12461.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12461:ℝ)) (by norm_num [ep12461]) ?_)
      (show bp12461^8 ≤ scalar12461.upperTail by norm_num [bp12461, scalar12461])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12461, bp12461, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12461:ℝ)) (by norm_num [em12461]) ?_)
      (show bm12461^8 ≤ scalar12461.lowerTail by norm_num [bm12461, scalar12461])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12461, bm12461, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12461 :
    agent12461.root+dsL+scalar12461.worldRadius < √(1/100/aL) ∧
    2*(agent12461.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12461, agent12461, scalar12461, tp12461, tm12461, ep12461, em12461, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12461, agent12461, scalar12461, tp12461, tm12461, ep12461, em12461, dsL]

noncomputable def master12461 : MasterCertificate 12461 world12461 agent12461 :=
  master scalar12461 dsL tp12461 tm12461 ep12461 em12461
    (by norm_num [dsL]) (by norm_num [tp12461]) (by norm_num [tm12461])
    (by norm_num [ep12461]) (by norm_num [em12461])
    positive12461 negative12461 tails12461.1 tails12461.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12461.1 tailGuards12461.2

theorem preserves12461 : master12461.toScalarCertificate = scalar12461 := rfl

noncomputable def tp12462 : ℝ := (2293435823 / 10000000000)
noncomputable def tm12462 : ℝ := (-((6011671521 / 10000000000)))
noncomputable def ep12462 : ℝ := (10146696740568909 / 20000000000000000000)
noncomputable def em12462 : ℝ := (49506704286640119 / 100000000000000000000)
noncomputable def bp12462 : ℝ := (2268541400346607369 / 5000000000000000000)
noncomputable def bm12462 : ℝ := (46246209320560821419 / 100000000000000000000)

theorem positive12462 :
    Eplus aL (agent12462.root+dsL) scalar12462.worldRadius world12462.frame
      agent12462.frame tp12462 ≤ -ep12462 := by
  apply positive_check (eT := (115517727399987147383 / 100000000000000000000)) (y := (2354987264690468329 / 6250000000000000000)) (u := (29152195751291534031 / 20000000000000000000))
  · norm_num [world12462, agent12462, scalar12462, tp12462, tm12462, ep12462, em12462, dsL]
  · norm_num [world12462, agent12462, scalar12462, tp12462, tm12462, ep12462, em12462, dsL]
  · norm_num [world12462, agent12462, scalar12462, tp12462, tm12462, ep12462, em12462, dsL]
  · norm_num [world12462, agent12462, scalar12462, tp12462, tm12462, ep12462, em12462, dsL]
  · norm_num [world12462, agent12462, scalar12462, tp12462, tm12462, ep12462, em12462, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12462, agent12462, tp12462, tm12462, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12462, agent12462, scalar12462, tp12462, tm12462, ep12462, em12462, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12462, agent12462, tp12462, tm12462, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12462, agent12462, scalar12462, tp12462, tm12462, ep12462, em12462, dsL]

theorem negative12462 :
    Eminus aL (agent12462.root+dsL) scalar12462.worldRadius world12462.frame
      agent12462.frame tm12462 ≤ -em12462 := by
  apply negative_check (lo := (68514451225456248817 / 100000000000000000000)) (hi := (34257225612728124409 / 50000000000000000000))
    (y := (-((71704895660824544767 / 100000000000000000000)))) (u := (48819080455401965231 / 100000000000000000000))
  · norm_num [world12462, agent12462, scalar12462, tp12462, tm12462, ep12462, em12462, dsL]
  · norm_num [world12462, agent12462, scalar12462, tp12462, tm12462, ep12462, em12462, dsL]
  · norm_num [world12462, agent12462, scalar12462, tp12462, tm12462, ep12462, em12462, dsL]
  · norm_num [world12462, agent12462, scalar12462, tp12462, tm12462, ep12462, em12462, dsL]
  · norm_num [world12462, agent12462, scalar12462, tp12462, tm12462, ep12462, em12462, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12462, agent12462, tp12462, tm12462, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12462, agent12462, tp12462, tm12462, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12462, agent12462, scalar12462, tp12462, tm12462, ep12462, em12462, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12462, agent12462, tp12462, tm12462, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12462, agent12462, scalar12462, tp12462, tm12462, ep12462, em12462, dsL]

theorem tails12462 :
    exp (-((12462:ℝ)*ep12462)) ≤ scalar12462.upperTail ∧
    exp (-((12462:ℝ)*em12462)) ≤ scalar12462.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12462:ℝ)) (by norm_num [ep12462]) ?_)
      (show bp12462^8 ≤ scalar12462.upperTail by norm_num [bp12462, scalar12462])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12462, bp12462, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12462:ℝ)) (by norm_num [em12462]) ?_)
      (show bm12462^8 ≤ scalar12462.lowerTail by norm_num [bm12462, scalar12462])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12462, bm12462, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12462 :
    agent12462.root+dsL+scalar12462.worldRadius < √(1/100/aL) ∧
    2*(agent12462.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12462, agent12462, scalar12462, tp12462, tm12462, ep12462, em12462, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12462, agent12462, scalar12462, tp12462, tm12462, ep12462, em12462, dsL]

noncomputable def master12462 : MasterCertificate 12462 world12462 agent12462 :=
  master scalar12462 dsL tp12462 tm12462 ep12462 em12462
    (by norm_num [dsL]) (by norm_num [tp12462]) (by norm_num [tm12462])
    (by norm_num [ep12462]) (by norm_num [em12462])
    positive12462 negative12462 tails12462.1 tails12462.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12462.1 tailGuards12462.2

theorem preserves12462 : master12462.toScalarCertificate = scalar12462 := rfl

noncomputable def tp12463 : ℝ := (2293529393 / 10000000000)
noncomputable def tm12463 : ℝ := (-((120237487 / 200000000)))
noncomputable def ep12463 : ℝ := (5073638694471043 / 10000000000000000000)
noncomputable def em12463 : ℝ := (49509212841025513 / 100000000000000000000)
noncomputable def bp12463 : ℝ := (11341474731948664967 / 25000000000000000000)
noncomputable def bm12463 : ℝ := (11560385094022411773 / 25000000000000000000)

theorem positive12463 :
    Eplus aL (agent12463.root+dsL) scalar12463.worldRadius world12463.frame
      agent12463.frame tp12463 ≤ -ep12463 := by
  apply positive_check (eT := (115518026088344580209 / 100000000000000000000)) (y := (18840336521403471207 / 50000000000000000000)) (u := (145762256805632664783 / 100000000000000000000))
  · norm_num [world12463, agent12463, scalar12463, tp12463, tm12463, ep12463, em12463, dsL]
  · norm_num [world12463, agent12463, scalar12463, tp12463, tm12463, ep12463, em12463, dsL]
  · norm_num [world12463, agent12463, scalar12463, tp12463, tm12463, ep12463, em12463, dsL]
  · norm_num [world12463, agent12463, scalar12463, tp12463, tm12463, ep12463, em12463, dsL]
  · norm_num [world12463, agent12463, scalar12463, tp12463, tm12463, ep12463, em12463, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12463, agent12463, tp12463, tm12463, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12463, agent12463, scalar12463, tp12463, tm12463, ep12463, em12463, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12463, agent12463, tp12463, tm12463, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12463, agent12463, scalar12463, tp12463, tm12463, ep12463, em12463, dsL]

theorem negative12463 :
    Eminus aL (agent12463.root+dsL) scalar12463.worldRadius world12463.frame
      agent12463.frame tm12463 ≤ -em12463 := by
  apply negative_check (lo := (17128542439061584037 / 25000000000000000000)) (hi := (68514169756246336149 / 100000000000000000000))
    (y := (-((14341012683687922949 / 20000000000000000000)))) (u := (6102374819718198619 / 12500000000000000000))
  · norm_num [world12463, agent12463, scalar12463, tp12463, tm12463, ep12463, em12463, dsL]
  · norm_num [world12463, agent12463, scalar12463, tp12463, tm12463, ep12463, em12463, dsL]
  · norm_num [world12463, agent12463, scalar12463, tp12463, tm12463, ep12463, em12463, dsL]
  · norm_num [world12463, agent12463, scalar12463, tp12463, tm12463, ep12463, em12463, dsL]
  · norm_num [world12463, agent12463, scalar12463, tp12463, tm12463, ep12463, em12463, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12463, agent12463, tp12463, tm12463, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12463, agent12463, tp12463, tm12463, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12463, agent12463, scalar12463, tp12463, tm12463, ep12463, em12463, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12463, agent12463, tp12463, tm12463, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12463, agent12463, scalar12463, tp12463, tm12463, ep12463, em12463, dsL]

theorem tails12463 :
    exp (-((12463:ℝ)*ep12463)) ≤ scalar12463.upperTail ∧
    exp (-((12463:ℝ)*em12463)) ≤ scalar12463.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12463:ℝ)) (by norm_num [ep12463]) ?_)
      (show bp12463^8 ≤ scalar12463.upperTail by norm_num [bp12463, scalar12463])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12463, bp12463, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12463:ℝ)) (by norm_num [em12463]) ?_)
      (show bm12463^8 ≤ scalar12463.lowerTail by norm_num [bm12463, scalar12463])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12463, bm12463, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12463 :
    agent12463.root+dsL+scalar12463.worldRadius < √(1/100/aL) ∧
    2*(agent12463.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12463, agent12463, scalar12463, tp12463, tm12463, ep12463, em12463, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12463, agent12463, scalar12463, tp12463, tm12463, ep12463, em12463, dsL]

noncomputable def master12463 : MasterCertificate 12463 world12463 agent12463 :=
  master scalar12463 dsL tp12463 tm12463 ep12463 em12463
    (by norm_num [dsL]) (by norm_num [tp12463]) (by norm_num [tm12463])
    (by norm_num [ep12463]) (by norm_num [em12463])
    positive12463 negative12463 tails12463.1 tails12463.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12463.1 tailGuards12463.2

theorem preserves12463 : master12463.toScalarCertificate = scalar12463 := rfl

noncomputable def tp12464 : ℝ := (1146811469 / 5000000000)
noncomputable def tm12464 : ℝ := (-((6012076633 / 10000000000)))
noncomputable def ep12464 : ℝ := (50739288537865887 / 100000000000000000000)
noncomputable def em12464 : ℝ := (9902343966900927 / 20000000000000000000)
noncomputable def bp12464 : ℝ := (22680485610049966787 / 50000000000000000000)
noncomputable def bm12464 : ℝ := (46236872737449268489 / 100000000000000000000)

theorem positive12464 :
    Eplus aL (agent12464.root+dsL) scalar12464.worldRadius world12464.frame
      agent12464.frame tp12464 ≤ -ep12464 := by
  apply positive_check (eT := (5775916231367027923 / 5000000000000000000)) (y := (37681549977556435879 / 100000000000000000000)) (u := (72881767525559460257 / 50000000000000000000))
  · norm_num [world12464, agent12464, scalar12464, tp12464, tm12464, ep12464, em12464, dsL]
  · norm_num [world12464, agent12464, scalar12464, tp12464, tm12464, ep12464, em12464, dsL]
  · norm_num [world12464, agent12464, scalar12464, tp12464, tm12464, ep12464, em12464, dsL]
  · norm_num [world12464, agent12464, scalar12464, tp12464, tm12464, ep12464, em12464, dsL]
  · norm_num [world12464, agent12464, scalar12464, tp12464, tm12464, ep12464, em12464, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12464, agent12464, tp12464, tm12464, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12464, agent12464, scalar12464, tp12464, tm12464, ep12464, em12464, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12464, agent12464, tp12464, tm12464, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12464, agent12464, scalar12464, tp12464, tm12464, ep12464, em12464, dsL]

theorem negative12464 :
    Eminus aL (agent12464.root+dsL) scalar12464.worldRadius world12464.frame
      agent12464.frame tm12464 ≤ -em12464 := by
  apply negative_check (lo := (68513890583683680483 / 100000000000000000000)) (hi := (17128472645920920121 / 25000000000000000000))
    (y := (-((35852613319330160583 / 50000000000000000000)))) (u := (48818918875333425257 / 100000000000000000000))
  · norm_num [world12464, agent12464, scalar12464, tp12464, tm12464, ep12464, em12464, dsL]
  · norm_num [world12464, agent12464, scalar12464, tp12464, tm12464, ep12464, em12464, dsL]
  · norm_num [world12464, agent12464, scalar12464, tp12464, tm12464, ep12464, em12464, dsL]
  · norm_num [world12464, agent12464, scalar12464, tp12464, tm12464, ep12464, em12464, dsL]
  · norm_num [world12464, agent12464, scalar12464, tp12464, tm12464, ep12464, em12464, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12464, agent12464, tp12464, tm12464, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12464, agent12464, tp12464, tm12464, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12464, agent12464, scalar12464, tp12464, tm12464, ep12464, em12464, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12464, agent12464, tp12464, tm12464, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12464, agent12464, scalar12464, tp12464, tm12464, ep12464, em12464, dsL]

theorem tails12464 :
    exp (-((12464:ℝ)*ep12464)) ≤ scalar12464.upperTail ∧
    exp (-((12464:ℝ)*em12464)) ≤ scalar12464.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12464:ℝ)) (by norm_num [ep12464]) ?_)
      (show bp12464^8 ≤ scalar12464.upperTail by norm_num [bp12464, scalar12464])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12464, bp12464, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12464:ℝ)) (by norm_num [em12464]) ?_)
      (show bm12464^8 ≤ scalar12464.lowerTail by norm_num [bm12464, scalar12464])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12464, bm12464, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12464 :
    agent12464.root+dsL+scalar12464.worldRadius < √(1/100/aL) ∧
    2*(agent12464.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12464, agent12464, scalar12464, tp12464, tm12464, ep12464, em12464, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12464, agent12464, scalar12464, tp12464, tm12464, ep12464, em12464, dsL]

noncomputable def master12464 : MasterCertificate 12464 world12464 agent12464 :=
  master scalar12464 dsL tp12464 tm12464 ep12464 em12464
    (by norm_num [dsL]) (by norm_num [tp12464]) (by norm_num [tm12464])
    (by norm_num [ep12464]) (by norm_num [em12464])
    positive12464 negative12464 tails12464.1 tails12464.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12464.1 tailGuards12464.2

theorem preserves12464 : master12464.toScalarCertificate = scalar12464 := rfl

noncomputable def tp12465 : ℝ := (2293716441 / 10000000000)
noncomputable def tm12465 : ℝ := (-((1503069747 / 2500000000)))
noncomputable def ep12465 : ℝ := (2537109415394361 / 5000000000000000000)
noncomputable def em12465 : ℝ := (24757112575728893 / 50000000000000000000)
noncomputable def bp12465 : ℝ := (45356045007063709901 / 100000000000000000000)
noncomputable def bm12465 : ℝ := (23116103243948656823 / 50000000000000000000)

theorem positive12465 :
    Eplus aL (agent12465.root+dsL) scalar12465.worldRadius world12465.frame
      agent12465.frame tp12465 ≤ -ep12465 := by
  apply positive_check (eT := (115518622893401788041 / 100000000000000000000)) (y := (2355151668037512003 / 6250000000000000000)) (u := (145764812981730354283 / 100000000000000000000))
  · norm_num [world12465, agent12465, scalar12465, tp12465, tm12465, ep12465, em12465, dsL]
  · norm_num [world12465, agent12465, scalar12465, tp12465, tm12465, ep12465, em12465, dsL]
  · norm_num [world12465, agent12465, scalar12465, tp12465, tm12465, ep12465, em12465, dsL]
  · norm_num [world12465, agent12465, scalar12465, tp12465, tm12465, ep12465, em12465, dsL]
  · norm_num [world12465, agent12465, scalar12465, tp12465, tm12465, ep12465, em12465, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12465, agent12465, tp12465, tm12465, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12465, agent12465, scalar12465, tp12465, tm12465, ep12465, em12465, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12465, agent12465, tp12465, tm12465, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12465, agent12465, scalar12465, tp12465, tm12465, ep12465, em12465, dsL]

theorem negative12465 :
    Eminus aL (agent12465.root+dsL) scalar12465.worldRadius world12465.frame
      agent12465.frame tm12465 ≤ -em12465 := by
  apply negative_check (lo := (34256805522330642571 / 50000000000000000000)) (hi := (68513611044661285143 / 100000000000000000000))
    (y := (-((71705391508142559103 / 100000000000000000000)))) (u := (48818838387900990961 / 100000000000000000000))
  · norm_num [world12465, agent12465, scalar12465, tp12465, tm12465, ep12465, em12465, dsL]
  · norm_num [world12465, agent12465, scalar12465, tp12465, tm12465, ep12465, em12465, dsL]
  · norm_num [world12465, agent12465, scalar12465, tp12465, tm12465, ep12465, em12465, dsL]
  · norm_num [world12465, agent12465, scalar12465, tp12465, tm12465, ep12465, em12465, dsL]
  · norm_num [world12465, agent12465, scalar12465, tp12465, tm12465, ep12465, em12465, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12465, agent12465, tp12465, tm12465, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12465, agent12465, tp12465, tm12465, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12465, agent12465, scalar12465, tp12465, tm12465, ep12465, em12465, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12465, agent12465, tp12465, tm12465, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12465, agent12465, scalar12465, tp12465, tm12465, ep12465, em12465, dsL]

theorem tails12465 :
    exp (-((12465:ℝ)*ep12465)) ≤ scalar12465.upperTail ∧
    exp (-((12465:ℝ)*em12465)) ≤ scalar12465.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12465:ℝ)) (by norm_num [ep12465]) ?_)
      (show bp12465^8 ≤ scalar12465.upperTail by norm_num [bp12465, scalar12465])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12465, bp12465, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12465:ℝ)) (by norm_num [em12465]) ?_)
      (show bm12465^8 ≤ scalar12465.lowerTail by norm_num [bm12465, scalar12465])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12465, bm12465, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12465 :
    agent12465.root+dsL+scalar12465.worldRadius < √(1/100/aL) ∧
    2*(agent12465.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12465, agent12465, scalar12465, tp12465, tm12465, ep12465, em12465, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12465, agent12465, scalar12465, tp12465, tm12465, ep12465, em12465, dsL]

noncomputable def master12465 : MasterCertificate 12465 world12465 agent12465 :=
  master scalar12465 dsL tp12465 tm12465 ep12465 em12465
    (by norm_num [dsL]) (by norm_num [tp12465]) (by norm_num [tm12465])
    (by norm_num [ep12465]) (by norm_num [em12465])
    positive12465 negative12465 tails12465.1 tails12465.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12465.1 tailGuards12465.2

theorem preserves12465 : master12465.toScalarCertificate = scalar12465 := rfl

noncomputable def tp12466 : ℝ := (573452467 / 2500000000)
noncomputable def tm12466 : ℝ := (-((6012481143 / 10000000000)))
noncomputable def ep12466 : ℝ := (50745087041401027 / 100000000000000000000)
noncomputable def em12466 : ℝ := (49516729490419143 / 100000000000000000000)
noncomputable def bp12466 : ℝ := (45351119732729033469 / 100000000000000000000)
noncomputable def bm12466 : ℝ := (11556885281054091853 / 25000000000000000000)

theorem positive12466 :
    Eplus aL (agent12466.root+dsL) scalar12466.worldRadius world12466.frame
      agent12466.frame tp12466 ≤ -ep12466 := by
  apply positive_check (eT := (23103784127912142139 / 20000000000000000000)) (y := (2355206401645226143 / 6250000000000000000)) (u := (14576608950477460577 / 10000000000000000000))
  · norm_num [world12466, agent12466, scalar12466, tp12466, tm12466, ep12466, em12466, dsL]
  · norm_num [world12466, agent12466, scalar12466, tp12466, tm12466, ep12466, em12466, dsL]
  · norm_num [world12466, agent12466, scalar12466, tp12466, tm12466, ep12466, em12466, dsL]
  · norm_num [world12466, agent12466, scalar12466, tp12466, tm12466, ep12466, em12466, dsL]
  · norm_num [world12466, agent12466, scalar12466, tp12466, tm12466, ep12466, em12466, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12466, agent12466, tp12466, tm12466, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12466, agent12466, scalar12466, tp12466, tm12466, ep12466, em12466, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12466, agent12466, tp12466, tm12466, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12466, agent12466, scalar12466, tp12466, tm12466, ep12466, em12466, dsL]

theorem negative12466 :
    Eminus aL (agent12466.root+dsL) scalar12466.worldRadius world12466.frame
      agent12466.frame tm12466 ≤ -em12466 := by
  apply negative_check (lo := (17128333077800199741 / 25000000000000000000)) (hi := (13702666462240159793 / 20000000000000000000))
    (y := (-((17926388768837353367 / 25000000000000000000)))) (u := (24409379268177963307 / 50000000000000000000))
  · norm_num [world12466, agent12466, scalar12466, tp12466, tm12466, ep12466, em12466, dsL]
  · norm_num [world12466, agent12466, scalar12466, tp12466, tm12466, ep12466, em12466, dsL]
  · norm_num [world12466, agent12466, scalar12466, tp12466, tm12466, ep12466, em12466, dsL]
  · norm_num [world12466, agent12466, scalar12466, tp12466, tm12466, ep12466, em12466, dsL]
  · norm_num [world12466, agent12466, scalar12466, tp12466, tm12466, ep12466, em12466, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12466, agent12466, tp12466, tm12466, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12466, agent12466, tp12466, tm12466, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12466, agent12466, scalar12466, tp12466, tm12466, ep12466, em12466, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12466, agent12466, tp12466, tm12466, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12466, agent12466, scalar12466, tp12466, tm12466, ep12466, em12466, dsL]

theorem tails12466 :
    exp (-((12466:ℝ)*ep12466)) ≤ scalar12466.upperTail ∧
    exp (-((12466:ℝ)*em12466)) ≤ scalar12466.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12466:ℝ)) (by norm_num [ep12466]) ?_)
      (show bp12466^8 ≤ scalar12466.upperTail by norm_num [bp12466, scalar12466])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12466, bp12466, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12466:ℝ)) (by norm_num [em12466]) ?_)
      (show bm12466^8 ≤ scalar12466.lowerTail by norm_num [bm12466, scalar12466])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12466, bm12466, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12466 :
    agent12466.root+dsL+scalar12466.worldRadius < √(1/100/aL) ∧
    2*(agent12466.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12466, agent12466, scalar12466, tp12466, tm12466, ep12466, em12466, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12466, agent12466, scalar12466, tp12466, tm12466, ep12466, em12466, dsL]

noncomputable def master12466 : MasterCertificate 12466 world12466 agent12466 :=
  master scalar12466 dsL tp12466 tm12466 ep12466 em12466
    (by norm_num [dsL]) (by norm_num [tp12466]) (by norm_num [tm12466])
    (by norm_num [ep12466]) (by norm_num [em12466])
    positive12466 negative12466 tails12466.1 tails12466.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12466.1 tailGuards12466.2

theorem preserves12466 : master12466.toScalarCertificate = scalar12466 := rfl

noncomputable def tp12467 : ℝ := (2293903283 / 10000000000)
noncomputable def tm12467 : ℝ := (-((3006341689 / 5000000000)))
noncomputable def ep12467 : ℝ := (50747983489490279 / 100000000000000000000)
noncomputable def em12467 : ℝ := (990384634502753 / 2000000000000000000)
noncomputable def bp12467 : ℝ := (2267309813982348459 / 5000000000000000000)
noncomputable def bm12467 : ℝ := (46222877457670453451 / 100000000000000000000)

theorem positive12467 :
    Eplus aL (agent12467.root+dsL) scalar12467.worldRadius world12467.frame
      agent12467.frame tp12467 ≤ -ep12467 := by
  apply positive_check (eT := (23103843666160538359 / 20000000000000000000)) (y := (301473428142950087 / 800000000000000000)) (u := (145767366554754497359 / 100000000000000000000))
  · norm_num [world12467, agent12467, scalar12467, tp12467, tm12467, ep12467, em12467, dsL]
  · norm_num [world12467, agent12467, scalar12467, tp12467, tm12467, ep12467, em12467, dsL]
  · norm_num [world12467, agent12467, scalar12467, tp12467, tm12467, ep12467, em12467, dsL]
  · norm_num [world12467, agent12467, scalar12467, tp12467, tm12467, ep12467, em12467, dsL]
  · norm_num [world12467, agent12467, scalar12467, tp12467, tm12467, ep12467, em12467, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12467, agent12467, tp12467, tm12467, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12467, agent12467, scalar12467, tp12467, tm12467, ep12467, em12467, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12467, agent12467, tp12467, tm12467, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12467, agent12467, scalar12467, tp12467, tm12467, ep12467, em12467, dsL]

theorem negative12467 :
    Eminus aL (agent12467.root+dsL) scalar12467.worldRadius world12467.frame
      agent12467.frame tm12467 ≤ -em12467 := by
  apply negative_check (lo := (68513053176778300957 / 100000000000000000000)) (hi := (34256526588389150479 / 50000000000000000000))
    (y := (-((71705720240940446253 / 100000000000000000000)))) (u := (12204669476157860781 / 25000000000000000000))
  · norm_num [world12467, agent12467, scalar12467, tp12467, tm12467, ep12467, em12467, dsL]
  · norm_num [world12467, agent12467, scalar12467, tp12467, tm12467, ep12467, em12467, dsL]
  · norm_num [world12467, agent12467, scalar12467, tp12467, tm12467, ep12467, em12467, dsL]
  · norm_num [world12467, agent12467, scalar12467, tp12467, tm12467, ep12467, em12467, dsL]
  · norm_num [world12467, agent12467, scalar12467, tp12467, tm12467, ep12467, em12467, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12467, agent12467, tp12467, tm12467, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12467, agent12467, tp12467, tm12467, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12467, agent12467, scalar12467, tp12467, tm12467, ep12467, em12467, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12467, agent12467, tp12467, tm12467, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12467, agent12467, scalar12467, tp12467, tm12467, ep12467, em12467, dsL]

theorem tails12467 :
    exp (-((12467:ℝ)*ep12467)) ≤ scalar12467.upperTail ∧
    exp (-((12467:ℝ)*em12467)) ≤ scalar12467.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12467:ℝ)) (by norm_num [ep12467]) ?_)
      (show bp12467^8 ≤ scalar12467.upperTail by norm_num [bp12467, scalar12467])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12467, bp12467, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12467:ℝ)) (by norm_num [em12467]) ?_)
      (show bm12467^8 ≤ scalar12467.lowerTail by norm_num [bm12467, scalar12467])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12467, bm12467, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12467 :
    agent12467.root+dsL+scalar12467.worldRadius < √(1/100/aL) ∧
    2*(agent12467.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12467, agent12467, scalar12467, tp12467, tm12467, ep12467, em12467, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12467, agent12467, scalar12467, tp12467, tm12467, ep12467, em12467, dsL]

noncomputable def master12467 : MasterCertificate 12467 world12467 agent12467 :=
  master scalar12467 dsL tp12467 tm12467 ep12467 em12467
    (by norm_num [dsL]) (by norm_num [tp12467]) (by norm_num [tm12467])
    (by norm_num [ep12467]) (by norm_num [em12467])
    positive12467 negative12467 tails12467.1 tails12467.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12467.1 tailGuards12467.2

theorem preserves12467 : master12467.toScalarCertificate = scalar12467 := rfl

noncomputable def tp12468 : ℝ := (1146998297 / 5000000000)
noncomputable def tm12468 : ℝ := (-((3006442673 / 5000000000)))
noncomputable def ep12468 : ℝ := (5075087937283947 / 10000000000000000000)
noncomputable def em12468 : ℝ := (49521733417898913 / 100000000000000000000)
noncomputable def bp12468 : ℝ := (2267063671590905239 / 5000000000000000000)
noncomputable def bm12468 : ℝ := (5777276795359286079 / 12500000000000000000)

theorem positive12468 :
    Eplus aL (agent12468.root+dsL) scalar12468.worldRadius world12468.frame
      agent12468.frame tp12468 ≤ -ep12468 := by
  apply positive_check (eT := (7219969706170817093 / 6250000000000000000)) (y := (18842526546522564347 / 50000000000000000000)) (u := (72884320702766193211 / 50000000000000000000))
  · norm_num [world12468, agent12468, scalar12468, tp12468, tm12468, ep12468, em12468, dsL]
  · norm_num [world12468, agent12468, scalar12468, tp12468, tm12468, ep12468, em12468, dsL]
  · norm_num [world12468, agent12468, scalar12468, tp12468, tm12468, ep12468, em12468, dsL]
  · norm_num [world12468, agent12468, scalar12468, tp12468, tm12468, ep12468, em12468, dsL]
  · norm_num [world12468, agent12468, scalar12468, tp12468, tm12468, ep12468, em12468, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12468, agent12468, tp12468, tm12468, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12468, agent12468, scalar12468, tp12468, tm12468, ep12468, em12468, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12468, agent12468, tp12468, tm12468, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12468, agent12468, scalar12468, tp12468, tm12468, ep12468, em12468, dsL]

theorem negative12468 :
    Eminus aL (agent12468.root+dsL) scalar12468.worldRadius world12468.frame
      agent12468.frame tm12468 ≤ -em12468 := by
  apply negative_check (lo := (2141024223018586783 / 3125000000000000000)) (hi := (68512775136594777057 / 100000000000000000000))
    (y := (-((8963235446799269151 / 12500000000000000000)))) (u := (6102324770932985771 / 12500000000000000000))
  · norm_num [world12468, agent12468, scalar12468, tp12468, tm12468, ep12468, em12468, dsL]
  · norm_num [world12468, agent12468, scalar12468, tp12468, tm12468, ep12468, em12468, dsL]
  · norm_num [world12468, agent12468, scalar12468, tp12468, tm12468, ep12468, em12468, dsL]
  · norm_num [world12468, agent12468, scalar12468, tp12468, tm12468, ep12468, em12468, dsL]
  · norm_num [world12468, agent12468, scalar12468, tp12468, tm12468, ep12468, em12468, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12468, agent12468, tp12468, tm12468, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12468, agent12468, tp12468, tm12468, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12468, agent12468, scalar12468, tp12468, tm12468, ep12468, em12468, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12468, agent12468, tp12468, tm12468, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12468, agent12468, scalar12468, tp12468, tm12468, ep12468, em12468, dsL]

theorem tails12468 :
    exp (-((12468:ℝ)*ep12468)) ≤ scalar12468.upperTail ∧
    exp (-((12468:ℝ)*em12468)) ≤ scalar12468.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12468:ℝ)) (by norm_num [ep12468]) ?_)
      (show bp12468^8 ≤ scalar12468.upperTail by norm_num [bp12468, scalar12468])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12468, bp12468, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12468:ℝ)) (by norm_num [em12468]) ?_)
      (show bm12468^8 ≤ scalar12468.lowerTail by norm_num [bm12468, scalar12468])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12468, bm12468, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12468 :
    agent12468.root+dsL+scalar12468.worldRadius < √(1/100/aL) ∧
    2*(agent12468.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12468, agent12468, scalar12468, tp12468, tm12468, ep12468, em12468, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12468, agent12468, scalar12468, tp12468, tm12468, ep12468, em12468, dsL]

noncomputable def master12468 : MasterCertificate 12468 world12468 agent12468 :=
  master scalar12468 dsL tp12468 tm12468 ep12468 em12468
    (by norm_num [dsL]) (by norm_num [tp12468]) (by norm_num [tm12468])
    (by norm_num [ep12468]) (by norm_num [em12468])
    positive12468 negative12468 tails12468.1 tails12468.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12468.1 tailGuards12468.2

theorem preserves12468 : master12468.toScalarCertificate = scalar12468 := rfl

noncomputable def tp12469 : ℝ := (573522477 / 2500000000)
noncomputable def tm12469 : ℝ := (-((601308721 / 1000000000)))
noncomputable def ep12469 : ℝ := (3172110830505201 / 6250000000000000000)
noncomputable def em12469 : ℝ := (12381058320901329 / 25000000000000000000)
noncomputable def bp12469 : ℝ := (45336352180908639549 / 100000000000000000000)
noncomputable def bm12469 : ℝ := (23106776382747165041 / 50000000000000000000)

theorem positive12469 :
    Eplus aL (agent12469.root+dsL) scalar12469.worldRadius world12469.frame
      agent12469.frame tp12469 ≤ -ep12469 := by
  apply positive_check (eT := (115519812320720009603 / 100000000000000000000)) (y := (9421482097240233429 / 25000000000000000000)) (u := (145769917318081130583 / 100000000000000000000))
  · norm_num [world12469, agent12469, scalar12469, tp12469, tm12469, ep12469, em12469, dsL]
  · norm_num [world12469, agent12469, scalar12469, tp12469, tm12469, ep12469, em12469, dsL]
  · norm_num [world12469, agent12469, scalar12469, tp12469, tm12469, ep12469, em12469, dsL]
  · norm_num [world12469, agent12469, scalar12469, tp12469, tm12469, ep12469, em12469, dsL]
  · norm_num [world12469, agent12469, scalar12469, tp12469, tm12469, ep12469, em12469, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12469, agent12469, tp12469, tm12469, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12469, agent12469, scalar12469, tp12469, tm12469, ep12469, em12469, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12469, agent12469, tp12469, tm12469, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12469, agent12469, scalar12469, tp12469, tm12469, ep12469, em12469, dsL]

theorem negative12469 :
    Eminus aL (agent12469.root+dsL) scalar12469.worldRadius world12469.frame
      agent12469.frame tm12469 ≤ -em12469 := by
  apply negative_check (lo := (8564062186034976331 / 12500000000000000000)) (hi := (68512497488279810649 / 100000000000000000000))
    (y := (-((17926511779071346429 / 25000000000000000000)))) (u := (48818518328670454853 / 100000000000000000000))
  · norm_num [world12469, agent12469, scalar12469, tp12469, tm12469, ep12469, em12469, dsL]
  · norm_num [world12469, agent12469, scalar12469, tp12469, tm12469, ep12469, em12469, dsL]
  · norm_num [world12469, agent12469, scalar12469, tp12469, tm12469, ep12469, em12469, dsL]
  · norm_num [world12469, agent12469, scalar12469, tp12469, tm12469, ep12469, em12469, dsL]
  · norm_num [world12469, agent12469, scalar12469, tp12469, tm12469, ep12469, em12469, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12469, agent12469, tp12469, tm12469, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12469, agent12469, tp12469, tm12469, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12469, agent12469, scalar12469, tp12469, tm12469, ep12469, em12469, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12469, agent12469, tp12469, tm12469, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12469, agent12469, scalar12469, tp12469, tm12469, ep12469, em12469, dsL]

theorem tails12469 :
    exp (-((12469:ℝ)*ep12469)) ≤ scalar12469.upperTail ∧
    exp (-((12469:ℝ)*em12469)) ≤ scalar12469.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12469:ℝ)) (by norm_num [ep12469]) ?_)
      (show bp12469^8 ≤ scalar12469.upperTail by norm_num [bp12469, scalar12469])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12469, bp12469, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12469:ℝ)) (by norm_num [em12469]) ?_)
      (show bm12469^8 ≤ scalar12469.lowerTail by norm_num [bm12469, scalar12469])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12469, bm12469, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12469 :
    agent12469.root+dsL+scalar12469.worldRadius < √(1/100/aL) ∧
    2*(agent12469.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12469, agent12469, scalar12469, tp12469, tm12469, ep12469, em12469, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12469, agent12469, scalar12469, tp12469, tm12469, ep12469, em12469, dsL]

noncomputable def master12469 : MasterCertificate 12469 world12469 agent12469 :=
  master scalar12469 dsL tp12469 tm12469 ep12469 em12469
    (by norm_num [dsL]) (by norm_num [tp12469]) (by norm_num [tm12469])
    (by norm_num [ep12469]) (by norm_num [em12469])
    positive12469 negative12469 tails12469.1 tails12469.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12469.1 tailGuards12469.2

theorem preserves12469 : master12469.toScalarCertificate = scalar12469 := rfl

noncomputable def tp12470 : ℝ := (573564893 / 2500000000)
noncomputable def tm12470 : ℝ := (-((3006759897 / 5000000000)))
noncomputable def ep12470 : ℝ := (50758136400323827 / 100000000000000000000)
noncomputable def em12470 : ℝ := (990566629879821 / 2000000000000000000)
noncomputable def bp12470 : ℝ := (45330393008056973203 / 100000000000000000000)
noncomputable def bm12470 : ℝ := (5775967513297876527 / 12500000000000000000)

theorem positive12470 :
    Eplus aL (agent12470.root+dsL) scalar12470.worldRadius world12470.frame
      agent12470.frame tp12470 ≤ -ep12470 := by
  apply positive_check (eT := (11552066403770217119 / 10000000000000000000)) (y := (37686070307514614081 / 100000000000000000000)) (u := (36442531048196571557 / 25000000000000000000))
  · norm_num [world12470, agent12470, scalar12470, tp12470, tm12470, ep12470, em12470, dsL]
  · norm_num [world12470, agent12470, scalar12470, tp12470, tm12470, ep12470, em12470, dsL]
  · norm_num [world12470, agent12470, scalar12470, tp12470, tm12470, ep12470, em12470, dsL]
  · norm_num [world12470, agent12470, scalar12470, tp12470, tm12470, ep12470, em12470, dsL]
  · norm_num [world12470, agent12470, scalar12470, tp12470, tm12470, ep12470, em12470, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12470, agent12470, tp12470, tm12470, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12470, agent12470, scalar12470, tp12470, tm12470, ep12470, em12470, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12470, agent12470, tp12470, tm12470, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12470, agent12470, scalar12470, tp12470, tm12470, ep12470, em12470, dsL]

theorem negative12470 :
    Eminus aL (agent12470.root+dsL) scalar12470.worldRadius world12470.frame
      agent12470.frame tm12470 ≤ -em12470 := by
  apply negative_check (lo := (68511225726364111077 / 100000000000000000000)) (hi := (34255612863182055539 / 50000000000000000000))
    (y := (-((71704274999124011779 / 100000000000000000000)))) (u := (48819383457677212861 / 100000000000000000000))
  · norm_num [world12470, agent12470, scalar12470, tp12470, tm12470, ep12470, em12470, dsL]
  · norm_num [world12470, agent12470, scalar12470, tp12470, tm12470, ep12470, em12470, dsL]
  · norm_num [world12470, agent12470, scalar12470, tp12470, tm12470, ep12470, em12470, dsL]
  · norm_num [world12470, agent12470, scalar12470, tp12470, tm12470, ep12470, em12470, dsL]
  · norm_num [world12470, agent12470, scalar12470, tp12470, tm12470, ep12470, em12470, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12470, agent12470, tp12470, tm12470, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12470, agent12470, tp12470, tm12470, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12470, agent12470, scalar12470, tp12470, tm12470, ep12470, em12470, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12470, agent12470, tp12470, tm12470, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12470, agent12470, scalar12470, tp12470, tm12470, ep12470, em12470, dsL]

theorem tails12470 :
    exp (-((12470:ℝ)*ep12470)) ≤ scalar12470.upperTail ∧
    exp (-((12470:ℝ)*em12470)) ≤ scalar12470.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12470:ℝ)) (by norm_num [ep12470]) ?_)
      (show bp12470^8 ≤ scalar12470.upperTail by norm_num [bp12470, scalar12470])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12470, bp12470, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12470:ℝ)) (by norm_num [em12470]) ?_)
      (show bm12470^8 ≤ scalar12470.lowerTail by norm_num [bm12470, scalar12470])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12470, bm12470, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12470 :
    agent12470.root+dsL+scalar12470.worldRadius < √(1/100/aL) ∧
    2*(agent12470.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12470, agent12470, scalar12470, tp12470, tm12470, ep12470, em12470, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12470, agent12470, scalar12470, tp12470, tm12470, ep12470, em12470, dsL]

noncomputable def master12470 : MasterCertificate 12470 world12470 agent12470 :=
  master scalar12470 dsL tp12470 tm12470 ep12470 em12470
    (by norm_num [dsL]) (by norm_num [tp12470]) (by norm_num [tm12470])
    (by norm_num [ep12470]) (by norm_num [em12470])
    positive12470 negative12470 tails12470.1 tails12470.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12470.1 tailGuards12470.2

theorem preserves12470 : master12470.toScalarCertificate = scalar12470 := rfl

noncomputable def tp12471 : ℝ := (458870559 / 2000000000)
noncomputable def tm12471 : ℝ := (-((37585759 / 62500000)))
noncomputable def ep12471 : ℝ := (25380513791974671 / 50000000000000000000)
noncomputable def em12471 : ℝ := (1981233153154043 / 4000000000000000000)
noncomputable def bp12471 : ℝ := (22662737064539514777 / 50000000000000000000)
noncomputable def bm12471 : ℝ := (46203080718462649343 / 100000000000000000000)

theorem positive12471 :
    Eplus aL (agent12471.root+dsL) scalar12471.worldRadius world12471.frame
      agent12471.frame tp12471 ≤ -ep12471 := by
  apply positive_check (eT := (7220060028244313749 / 6250000000000000000)) (y := (37686944786665082503 / 100000000000000000000)) (u := (36442849731925900371 / 25000000000000000000))
  · norm_num [world12471, agent12471, scalar12471, tp12471, tm12471, ep12471, em12471, dsL]
  · norm_num [world12471, agent12471, scalar12471, tp12471, tm12471, ep12471, em12471, dsL]
  · norm_num [world12471, agent12471, scalar12471, tp12471, tm12471, ep12471, em12471, dsL]
  · norm_num [world12471, agent12471, scalar12471, tp12471, tm12471, ep12471, em12471, dsL]
  · norm_num [world12471, agent12471, scalar12471, tp12471, tm12471, ep12471, em12471, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12471, agent12471, tp12471, tm12471, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12471, agent12471, scalar12471, tp12471, tm12471, ep12471, em12471, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12471, agent12471, tp12471, tm12471, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12471, agent12471, scalar12471, tp12471, tm12471, ep12471, em12471, dsL]

theorem negative12471 :
    Eminus aL (agent12471.root+dsL) scalar12471.worldRadius world12471.frame
      agent12471.frame tm12471 ≤ -em12471 := by
  apply negative_check (lo := (13702189786295024599 / 20000000000000000000)) (hi := (17127737232868780749 / 25000000000000000000))
    (y := (-((71704437870378005923 / 100000000000000000000)))) (u := (48819303944999934797 / 100000000000000000000))
  · norm_num [world12471, agent12471, scalar12471, tp12471, tm12471, ep12471, em12471, dsL]
  · norm_num [world12471, agent12471, scalar12471, tp12471, tm12471, ep12471, em12471, dsL]
  · norm_num [world12471, agent12471, scalar12471, tp12471, tm12471, ep12471, em12471, dsL]
  · norm_num [world12471, agent12471, scalar12471, tp12471, tm12471, ep12471, em12471, dsL]
  · norm_num [world12471, agent12471, scalar12471, tp12471, tm12471, ep12471, em12471, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12471, agent12471, tp12471, tm12471, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12471, agent12471, tp12471, tm12471, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12471, agent12471, scalar12471, tp12471, tm12471, ep12471, em12471, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12471, agent12471, tp12471, tm12471, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12471, agent12471, scalar12471, tp12471, tm12471, ep12471, em12471, dsL]

theorem tails12471 :
    exp (-((12471:ℝ)*ep12471)) ≤ scalar12471.upperTail ∧
    exp (-((12471:ℝ)*em12471)) ≤ scalar12471.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12471:ℝ)) (by norm_num [ep12471]) ?_)
      (show bp12471^8 ≤ scalar12471.upperTail by norm_num [bp12471, scalar12471])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12471, bp12471, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12471:ℝ)) (by norm_num [em12471]) ?_)
      (show bm12471^8 ≤ scalar12471.lowerTail by norm_num [bm12471, scalar12471])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12471, bm12471, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12471 :
    agent12471.root+dsL+scalar12471.worldRadius < √(1/100/aL) ∧
    2*(agent12471.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12471, agent12471, scalar12471, tp12471, tm12471, ep12471, em12471, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12471, agent12471, scalar12471, tp12471, tm12471, ep12471, em12471, dsL]

noncomputable def master12471 : MasterCertificate 12471 world12471 agent12471 :=
  master scalar12471 dsL tp12471 tm12471 ep12471 em12471
    (by norm_num [dsL]) (by norm_num [tp12471]) (by norm_num [tm12471])
    (by norm_num [ep12471]) (by norm_num [em12471])
    positive12471 negative12471 tails12471.1 tails12471.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12471.1 tailGuards12471.2

theorem preserves12471 : master12471.toScalarCertificate = scalar12471 := rfl

noncomputable def tp12472 : ℝ := (1147222979 / 5000000000)
noncomputable def tm12472 : ℝ := (-((6013922919 / 10000000000)))
noncomputable def ep12472 : ℝ := (1015278345381831 / 2000000000000000000)
noncomputable def em12472 : ℝ := (49533324758471147 / 100000000000000000000)
noncomputable def bp12472 : ℝ := (11330139128757894153 / 25000000000000000000)
noncomputable def bm12472 : ℝ := (23099211262021581731 / 50000000000000000000)

theorem positive12472 :
    Eplus aL (agent12472.root+dsL) scalar12472.worldRadius world12472.frame
      agent12472.frame tp12472 ≤ -ep12472 := by
  apply positive_check (eT := (11552125646253541107 / 10000000000000000000)) (y := (18843909311109819651 / 50000000000000000000)) (u := (145772672735581291547 / 100000000000000000000))
  · norm_num [world12472, agent12472, scalar12472, tp12472, tm12472, ep12472, em12472, dsL]
  · norm_num [world12472, agent12472, scalar12472, tp12472, tm12472, ep12472, em12472, dsL]
  · norm_num [world12472, agent12472, scalar12472, tp12472, tm12472, ep12472, em12472, dsL]
  · norm_num [world12472, agent12472, scalar12472, tp12472, tm12472, ep12472, em12472, dsL]
  · norm_num [world12472, agent12472, scalar12472, tp12472, tm12472, ep12472, em12472, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12472, agent12472, tp12472, tm12472, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12472, agent12472, scalar12472, tp12472, tm12472, ep12472, em12472, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12472, agent12472, tp12472, tm12472, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12472, agent12472, scalar12472, tp12472, tm12472, ep12472, em12472, dsL]

theorem negative12472 :
    Eminus aL (agent12472.root+dsL) scalar12472.worldRadius world12472.frame
      agent12472.frame tm12472 ≤ -em12472 := by
  apply negative_check (lo := (68510672799767230433 / 100000000000000000000)) (hi := (34255336399883615217 / 50000000000000000000))
    (y := (-((71704599632545427479 / 100000000000000000000)))) (u := (48819224973899625947 / 100000000000000000000))
  · norm_num [world12472, agent12472, scalar12472, tp12472, tm12472, ep12472, em12472, dsL]
  · norm_num [world12472, agent12472, scalar12472, tp12472, tm12472, ep12472, em12472, dsL]
  · norm_num [world12472, agent12472, scalar12472, tp12472, tm12472, ep12472, em12472, dsL]
  · norm_num [world12472, agent12472, scalar12472, tp12472, tm12472, ep12472, em12472, dsL]
  · norm_num [world12472, agent12472, scalar12472, tp12472, tm12472, ep12472, em12472, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12472, agent12472, tp12472, tm12472, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12472, agent12472, tp12472, tm12472, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12472, agent12472, scalar12472, tp12472, tm12472, ep12472, em12472, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12472, agent12472, tp12472, tm12472, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12472, agent12472, scalar12472, tp12472, tm12472, ep12472, em12472, dsL]

theorem tails12472 :
    exp (-((12472:ℝ)*ep12472)) ≤ scalar12472.upperTail ∧
    exp (-((12472:ℝ)*em12472)) ≤ scalar12472.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12472:ℝ)) (by norm_num [ep12472]) ?_)
      (show bp12472^8 ≤ scalar12472.upperTail by norm_num [bp12472, scalar12472])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12472, bp12472, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12472:ℝ)) (by norm_num [em12472]) ?_)
      (show bm12472^8 ≤ scalar12472.lowerTail by norm_num [bm12472, scalar12472])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12472, bm12472, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12472 :
    agent12472.root+dsL+scalar12472.worldRadius < √(1/100/aL) ∧
    2*(agent12472.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12472, agent12472, scalar12472, tp12472, tm12472, ep12472, em12472, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12472, agent12472, scalar12472, tp12472, tm12472, ep12472, em12472, dsL]

noncomputable def master12472 : MasterCertificate 12472 world12472 agent12472 :=
  master scalar12472 dsL tp12472 tm12472 ep12472 em12472
    (by norm_num [dsL]) (by norm_num [tp12472]) (by norm_num [tm12472])
    (by norm_num [ep12472]) (by norm_num [em12472])
    positive12472 negative12472 tails12472.1 tails12472.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12472.1 tailGuards12472.2

theorem preserves12472 : master12472.toScalarCertificate = scalar12472 := rfl

noncomputable def tp12473 : ℝ := (2294539049 / 10000000000)
noncomputable def tm12473 : ℝ := (-((6014124463 / 10000000000)))
noncomputable def ep12473 : ℝ := (25383402567993481 / 50000000000000000000)
noncomputable def em12473 : ℝ := (1981432760647477 / 4000000000000000000)
noncomputable def bp12473 : ℝ := (22657820195897520839 / 50000000000000000000)
noncomputable def bm12473 : ℝ := (11548441428789581867 / 25000000000000000000)

theorem positive12473 :
    Eplus aL (agent12473.root+dsL) scalar12473.worldRadius world12473.frame
      agent12473.frame tp12473 ≤ -ep12473 := by
  apply positive_check (eT := (57760775991208730209 / 50000000000000000000)) (y := (7537738340650974511 / 20000000000000000000)) (u := (72886972727348712537 / 50000000000000000000))
  · norm_num [world12473, agent12473, scalar12473, tp12473, tm12473, ep12473, em12473, dsL]
  · norm_num [world12473, agent12473, scalar12473, tp12473, tm12473, ep12473, em12473, dsL]
  · norm_num [world12473, agent12473, scalar12473, tp12473, tm12473, ep12473, em12473, dsL]
  · norm_num [world12473, agent12473, scalar12473, tp12473, tm12473, ep12473, em12473, dsL]
  · norm_num [world12473, agent12473, scalar12473, tp12473, tm12473, ep12473, em12473, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12473, agent12473, tp12473, tm12473, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12473, agent12473, scalar12473, tp12473, tm12473, ep12473, em12473, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12473, agent12473, tp12473, tm12473, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12473, agent12473, scalar12473, tp12473, tm12473, ep12473, em12473, dsL]

theorem negative12473 :
    Eminus aL (agent12473.root+dsL) scalar12473.worldRadius world12473.frame
      agent12473.frame tm12473 ≤ -em12473 := by
  apply negative_check (lo := (68510396331730227071 / 100000000000000000000)) (hi := (535237471341642399 / 781250000000000000))
    (y := (-((1792619074283988929 / 2500000000000000000)))) (u := (9763829046644322007 / 20000000000000000000))
  · norm_num [world12473, agent12473, scalar12473, tp12473, tm12473, ep12473, em12473, dsL]
  · norm_num [world12473, agent12473, scalar12473, tp12473, tm12473, ep12473, em12473, dsL]
  · norm_num [world12473, agent12473, scalar12473, tp12473, tm12473, ep12473, em12473, dsL]
  · norm_num [world12473, agent12473, scalar12473, tp12473, tm12473, ep12473, em12473, dsL]
  · norm_num [world12473, agent12473, scalar12473, tp12473, tm12473, ep12473, em12473, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12473, agent12473, tp12473, tm12473, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12473, agent12473, tp12473, tm12473, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12473, agent12473, scalar12473, tp12473, tm12473, ep12473, em12473, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12473, agent12473, tp12473, tm12473, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12473, agent12473, scalar12473, tp12473, tm12473, ep12473, em12473, dsL]

theorem tails12473 :
    exp (-((12473:ℝ)*ep12473)) ≤ scalar12473.upperTail ∧
    exp (-((12473:ℝ)*em12473)) ≤ scalar12473.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12473:ℝ)) (by norm_num [ep12473]) ?_)
      (show bp12473^8 ≤ scalar12473.upperTail by norm_num [bp12473, scalar12473])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12473, bp12473, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12473:ℝ)) (by norm_num [em12473]) ?_)
      (show bm12473^8 ≤ scalar12473.lowerTail by norm_num [bm12473, scalar12473])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12473, bm12473, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12473 :
    agent12473.root+dsL+scalar12473.worldRadius < √(1/100/aL) ∧
    2*(agent12473.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12473, agent12473, scalar12473, tp12473, tm12473, ep12473, em12473, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12473, agent12473, scalar12473, tp12473, tm12473, ep12473, em12473, dsL]

noncomputable def master12473 : MasterCertificate 12473 world12473 agent12473 :=
  master scalar12473 dsL tp12473 tm12473 ep12473 em12473
    (by norm_num [dsL]) (by norm_num [tp12473]) (by norm_num [tm12473])
    (by norm_num [ep12473]) (by norm_num [em12473])
    positive12473 negative12473 tails12473.1 tails12473.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12473.1 tailGuards12473.2

theorem preserves12473 : master12473.toScalarCertificate = scalar12473 := rfl

noncomputable def tp12474 : ℝ := (2294632151 / 10000000000)
noncomputable def tm12474 : ℝ := (-((1503581439 / 2500000000)))
noncomputable def ep12474 : ℝ := (50769692298145867 / 100000000000000000000)
noncomputable def em12474 : ℝ := (24769156292886817 / 50000000000000000000)
noncomputable def bp12474 : ℝ := (22655362486302806619 / 50000000000000000000)
noncomputable def bm12474 : ℝ := (46189109583254860449 / 100000000000000000000)

theorem positive12474 :
    Eplus aL (agent12474.root+dsL) scalar12474.worldRadius world12474.frame
      agent12474.frame tp12474 ≤ -ep12474 := by
  apply positive_check (eT := (23104369522904114701 / 20000000000000000000)) (y := (753791308934543317 / 2000000000000000000)) (u := (145775219150594549157 / 100000000000000000000))
  · norm_num [world12474, agent12474, scalar12474, tp12474, tm12474, ep12474, em12474, dsL]
  · norm_num [world12474, agent12474, scalar12474, tp12474, tm12474, ep12474, em12474, dsL]
  · norm_num [world12474, agent12474, scalar12474, tp12474, tm12474, ep12474, em12474, dsL]
  · norm_num [world12474, agent12474, scalar12474, tp12474, tm12474, ep12474, em12474, dsL]
  · norm_num [world12474, agent12474, scalar12474, tp12474, tm12474, ep12474, em12474, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12474, agent12474, tp12474, tm12474, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12474, agent12474, scalar12474, tp12474, tm12474, ep12474, em12474, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12474, agent12474, tp12474, tm12474, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12474, agent12474, scalar12474, tp12474, tm12474, ep12474, em12474, dsL]

theorem negative12474 :
    Eminus aL (agent12474.root+dsL) scalar12474.worldRadius world12474.frame
      agent12474.frame tm12474 ≤ -em12474 := by
  apply negative_check (lo := (1712753022217690551 / 2500000000000000000)) (hi := (68510120888707622041 / 100000000000000000000))
    (y := (-((71704924921085859663 / 100000000000000000000)))) (u := (9763813234162708461 / 20000000000000000000))
  · norm_num [world12474, agent12474, scalar12474, tp12474, tm12474, ep12474, em12474, dsL]
  · norm_num [world12474, agent12474, scalar12474, tp12474, tm12474, ep12474, em12474, dsL]
  · norm_num [world12474, agent12474, scalar12474, tp12474, tm12474, ep12474, em12474, dsL]
  · norm_num [world12474, agent12474, scalar12474, tp12474, tm12474, ep12474, em12474, dsL]
  · norm_num [world12474, agent12474, scalar12474, tp12474, tm12474, ep12474, em12474, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12474, agent12474, tp12474, tm12474, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12474, agent12474, tp12474, tm12474, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12474, agent12474, scalar12474, tp12474, tm12474, ep12474, em12474, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12474, agent12474, tp12474, tm12474, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12474, agent12474, scalar12474, tp12474, tm12474, ep12474, em12474, dsL]

theorem tails12474 :
    exp (-((12474:ℝ)*ep12474)) ≤ scalar12474.upperTail ∧
    exp (-((12474:ℝ)*em12474)) ≤ scalar12474.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12474:ℝ)) (by norm_num [ep12474]) ?_)
      (show bp12474^8 ≤ scalar12474.upperTail by norm_num [bp12474, scalar12474])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12474, bp12474, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12474:ℝ)) (by norm_num [em12474]) ?_)
      (show bm12474^8 ≤ scalar12474.lowerTail by norm_num [bm12474, scalar12474])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12474, bm12474, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12474 :
    agent12474.root+dsL+scalar12474.worldRadius < √(1/100/aL) ∧
    2*(agent12474.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12474, agent12474, scalar12474, tp12474, tm12474, ep12474, em12474, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12474, agent12474, scalar12474, tp12474, tm12474, ep12474, em12474, dsL]

noncomputable def master12474 : MasterCertificate 12474 world12474 agent12474 :=
  master scalar12474 dsL tp12474 tm12474 ep12474 em12474
    (by norm_num [dsL]) (by norm_num [tp12474]) (by norm_num [tm12474])
    (by norm_num [ep12474]) (by norm_num [em12474])
    positive12474 negative12474 tails12474.1 tails12474.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12474.1 tailGuards12474.2

theorem preserves12474 : master12474.toScalarCertificate = scalar12474 := rfl

end BstLean.Part268
