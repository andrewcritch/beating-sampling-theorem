import BstLean.Part261Checker
import BstLean.Part281Scalar9
namespace BstLean.Part281
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12084 : ℝ := (1183207113 / 5000000000)
noncomputable def tm12084 : ℝ := (-((6124404581 / 10000000000)))
noncomputable def ep12084 : ℝ := (54405340523347557 / 100000000000000000000)
noncomputable def em12084 : ℝ := (10494730111811601 / 20000000000000000000)
noncomputable def bp12084 : ℝ := (43964281378250081849 / 100000000000000000000)
noncomputable def bm12084 : ℝ := (9053195432534882143 / 20000000000000000000)

theorem positive12084 :
    Eplus aL (agent12084.root+dsL) scalar12084.worldRadius world12084.frame
      agent12084.frame tp12084 ≤ -ep12084 := by
  apply positive_check (eT := (23240691496433649071 / 20000000000000000000)) (y := (7917010331137482971 / 20000000000000000000)) (u := (37141180532250937987 / 25000000000000000000))
  · norm_num [world12084, agent12084, scalar12084, tp12084, tm12084, ep12084, em12084, dsL]
  · norm_num [world12084, agent12084, scalar12084, tp12084, tm12084, ep12084, em12084, dsL]
  · norm_num [world12084, agent12084, scalar12084, tp12084, tm12084, ep12084, em12084, dsL]
  · norm_num [world12084, agent12084, scalar12084, tp12084, tm12084, ep12084, em12084, dsL]
  · norm_num [world12084, agent12084, scalar12084, tp12084, tm12084, ep12084, em12084, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12084, agent12084, tp12084, tm12084, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12084, agent12084, scalar12084, tp12084, tm12084, ep12084, em12084, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12084, agent12084, tp12084, tm12084, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12084, agent12084, scalar12084, tp12084, tm12084, ep12084, em12084, dsL]

theorem negative12084 :
    Eminus aL (agent12084.root+dsL) scalar12084.worldRadius world12084.frame
      agent12084.frame tm12084 ≤ -em12084 := by
  apply negative_check (lo := (4237304581568479927 / 6250000000000000000)) (hi := (67796873305095678833 / 100000000000000000000))
    (y := (-((14665822960102838893 / 20000000000000000000)))) (u := (96065112670788007 / 200000000000000000))
  · norm_num [world12084, agent12084, scalar12084, tp12084, tm12084, ep12084, em12084, dsL]
  · norm_num [world12084, agent12084, scalar12084, tp12084, tm12084, ep12084, em12084, dsL]
  · norm_num [world12084, agent12084, scalar12084, tp12084, tm12084, ep12084, em12084, dsL]
  · norm_num [world12084, agent12084, scalar12084, tp12084, tm12084, ep12084, em12084, dsL]
  · norm_num [world12084, agent12084, scalar12084, tp12084, tm12084, ep12084, em12084, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12084, agent12084, tp12084, tm12084, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12084, agent12084, tp12084, tm12084, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12084, agent12084, scalar12084, tp12084, tm12084, ep12084, em12084, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12084, agent12084, tp12084, tm12084, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12084, agent12084, scalar12084, tp12084, tm12084, ep12084, em12084, dsL]

theorem tails12084 :
    exp (-((12084:ℝ)*ep12084)) ≤ scalar12084.upperTail ∧
    exp (-((12084:ℝ)*em12084)) ≤ scalar12084.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12084:ℝ)) (by norm_num [ep12084]) ?_)
      (show bp12084^8 ≤ scalar12084.upperTail by norm_num [bp12084, scalar12084])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12084, bp12084, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12084:ℝ)) (by norm_num [em12084]) ?_)
      (show bm12084^8 ≤ scalar12084.lowerTail by norm_num [bm12084, scalar12084])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12084, bm12084, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12084 :
    agent12084.root+dsL+scalar12084.worldRadius < √(1/100/aL) ∧
    2*(agent12084.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12084, agent12084, scalar12084, tp12084, tm12084, ep12084, em12084, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12084, agent12084, scalar12084, tp12084, tm12084, ep12084, em12084, dsL]

noncomputable def master12084 : MasterCertificate 12084 world12084 agent12084 :=
  master scalar12084 dsL tp12084 tm12084 ep12084 em12084
    (by norm_num [dsL]) (by norm_num [tp12084]) (by norm_num [tm12084])
    (by norm_num [ep12084]) (by norm_num [em12084])
    positive12084 negative12084 tails12084.1 tails12084.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12084.1 tailGuards12084.2

theorem preserves12084 : master12084.toScalarCertificate = scalar12084 := rfl

noncomputable def tp12085 : ℝ := (2366515557 / 10000000000)
noncomputable def tm12085 : ℝ := (-((6124632143 / 10000000000)))
noncomputable def ep12085 : ℝ := (54408323991294971 / 100000000000000000000)
noncomputable def em12085 : ℝ := (26238124025665447 / 50000000000000000000)
noncomputable def bp12085 : ℝ := (43959310367926594757 / 100000000000000000000)
noncomputable def bm12085 : ℝ := (11315308039875121107 / 25000000000000000000)

theorem positive12085 :
    Eplus aL (agent12085.root+dsL) scalar12085.worldRadius world12085.frame
      agent12085.frame tp12085 ≤ -ep12085 := by
  apply positive_check (eT := (58101891625377243981 / 50000000000000000000)) (y := (39585703749211618129 / 100000000000000000000)) (u := (148565690913094691497 / 100000000000000000000))
  · norm_num [world12085, agent12085, scalar12085, tp12085, tm12085, ep12085, em12085, dsL]
  · norm_num [world12085, agent12085, scalar12085, tp12085, tm12085, ep12085, em12085, dsL]
  · norm_num [world12085, agent12085, scalar12085, tp12085, tm12085, ep12085, em12085, dsL]
  · norm_num [world12085, agent12085, scalar12085, tp12085, tm12085, ep12085, em12085, dsL]
  · norm_num [world12085, agent12085, scalar12085, tp12085, tm12085, ep12085, em12085, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12085, agent12085, tp12085, tm12085, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12085, agent12085, scalar12085, tp12085, tm12085, ep12085, em12085, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12085, agent12085, tp12085, tm12085, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12085, agent12085, scalar12085, tp12085, tm12085, ep12085, em12085, dsL]

theorem negative12085 :
    Eminus aL (agent12085.root+dsL) scalar12085.worldRadius world12085.frame
      agent12085.frame tm12085 ≤ -em12085 := by
  apply negative_check (lo := (8474566331044500889 / 12500000000000000000)) (hi := (67796530648356007113 / 100000000000000000000))
    (y := (-((36664368673308174097 / 50000000000000000000)))) (u := (24016368818246145233 / 50000000000000000000))
  · norm_num [world12085, agent12085, scalar12085, tp12085, tm12085, ep12085, em12085, dsL]
  · norm_num [world12085, agent12085, scalar12085, tp12085, tm12085, ep12085, em12085, dsL]
  · norm_num [world12085, agent12085, scalar12085, tp12085, tm12085, ep12085, em12085, dsL]
  · norm_num [world12085, agent12085, scalar12085, tp12085, tm12085, ep12085, em12085, dsL]
  · norm_num [world12085, agent12085, scalar12085, tp12085, tm12085, ep12085, em12085, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12085, agent12085, tp12085, tm12085, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12085, agent12085, tp12085, tm12085, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12085, agent12085, scalar12085, tp12085, tm12085, ep12085, em12085, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12085, agent12085, tp12085, tm12085, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12085, agent12085, scalar12085, tp12085, tm12085, ep12085, em12085, dsL]

theorem tails12085 :
    exp (-((12085:ℝ)*ep12085)) ≤ scalar12085.upperTail ∧
    exp (-((12085:ℝ)*em12085)) ≤ scalar12085.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12085:ℝ)) (by norm_num [ep12085]) ?_)
      (show bp12085^8 ≤ scalar12085.upperTail by norm_num [bp12085, scalar12085])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12085, bp12085, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12085:ℝ)) (by norm_num [em12085]) ?_)
      (show bm12085^8 ≤ scalar12085.lowerTail by norm_num [bm12085, scalar12085])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12085, bm12085, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12085 :
    agent12085.root+dsL+scalar12085.worldRadius < √(1/100/aL) ∧
    2*(agent12085.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12085, agent12085, scalar12085, tp12085, tm12085, ep12085, em12085, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12085, agent12085, scalar12085, tp12085, tm12085, ep12085, em12085, dsL]

noncomputable def master12085 : MasterCertificate 12085 world12085 agent12085 :=
  master scalar12085 dsL tp12085 tm12085 ep12085 em12085
    (by norm_num [dsL]) (by norm_num [tp12085]) (by norm_num [tm12085])
    (by norm_num [ep12085]) (by norm_num [em12085])
    positive12085 negative12085 tails12085.1 tails12085.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12085.1 tailGuards12085.2

theorem preserves12085 : master12085.toScalarCertificate = scalar12085 := rfl

noncomputable def tp12086 : ℝ := (2366616813 / 10000000000)
noncomputable def tm12086 : ℝ := (-((3062429891 / 5000000000)))
noncomputable def ep12086 : ℝ := (54411306256345147 / 100000000000000000000)
noncomputable def em12086 : ℝ := (52478844408417503 / 100000000000000000000)
noncomputable def bp12086 : ℝ := (21977170195301472807 / 50000000000000000000)
noncomputable def bm12086 : ℝ := (22628244067989347649 / 50000000000000000000)

theorem positive12086 :
    Eplus aL (agent12086.root+dsL) scalar12086.worldRadius world12086.frame
      agent12086.frame tp12086 ≤ -ep12086 := by
  apply positive_check (eT := (23240821700594876051 / 20000000000000000000)) (y := (7917271027506909381 / 20000000000000000000)) (u := (2971333173116181119 / 2000000000000000000))
  · norm_num [world12086, agent12086, scalar12086, tp12086, tm12086, ep12086, em12086, dsL]
  · norm_num [world12086, agent12086, scalar12086, tp12086, tm12086, ep12086, em12086, dsL]
  · norm_num [world12086, agent12086, scalar12086, tp12086, tm12086, ep12086, em12086, dsL]
  · norm_num [world12086, agent12086, scalar12086, tp12086, tm12086, ep12086, em12086, dsL]
  · norm_num [world12086, agent12086, scalar12086, tp12086, tm12086, ep12086, em12086, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12086, agent12086, tp12086, tm12086, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12086, agent12086, scalar12086, tp12086, tm12086, ep12086, em12086, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12086, agent12086, tp12086, tm12086, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12086, agent12086, scalar12086, tp12086, tm12086, ep12086, em12086, dsL]

theorem negative12086 :
    Eminus aL (agent12086.root+dsL) scalar12086.worldRadius world12086.frame
      agent12086.frame tm12086 ≤ -em12086 := by
  apply negative_check (lo := (16949046900218011273 / 25000000000000000000)) (hi := (67796187600872045093 / 100000000000000000000))
    (y := (-((73328362039500431133 / 100000000000000000000)))) (u := (750514342298638969 / 1562500000000000000))
  · norm_num [world12086, agent12086, scalar12086, tp12086, tm12086, ep12086, em12086, dsL]
  · norm_num [world12086, agent12086, scalar12086, tp12086, tm12086, ep12086, em12086, dsL]
  · norm_num [world12086, agent12086, scalar12086, tp12086, tm12086, ep12086, em12086, dsL]
  · norm_num [world12086, agent12086, scalar12086, tp12086, tm12086, ep12086, em12086, dsL]
  · norm_num [world12086, agent12086, scalar12086, tp12086, tm12086, ep12086, em12086, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12086, agent12086, tp12086, tm12086, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12086, agent12086, tp12086, tm12086, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12086, agent12086, scalar12086, tp12086, tm12086, ep12086, em12086, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12086, agent12086, tp12086, tm12086, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12086, agent12086, scalar12086, tp12086, tm12086, ep12086, em12086, dsL]

theorem tails12086 :
    exp (-((12086:ℝ)*ep12086)) ≤ scalar12086.upperTail ∧
    exp (-((12086:ℝ)*em12086)) ≤ scalar12086.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12086:ℝ)) (by norm_num [ep12086]) ?_)
      (show bp12086^8 ≤ scalar12086.upperTail by norm_num [bp12086, scalar12086])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12086, bp12086, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12086:ℝ)) (by norm_num [em12086]) ?_)
      (show bm12086^8 ≤ scalar12086.lowerTail by norm_num [bm12086, scalar12086])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12086, bm12086, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12086 :
    agent12086.root+dsL+scalar12086.worldRadius < √(1/100/aL) ∧
    2*(agent12086.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12086, agent12086, scalar12086, tp12086, tm12086, ep12086, em12086, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12086, agent12086, scalar12086, tp12086, tm12086, ep12086, em12086, dsL]

noncomputable def master12086 : MasterCertificate 12086 world12086 agent12086 :=
  master scalar12086 dsL tp12086 tm12086 ep12086 em12086
    (by norm_num [dsL]) (by norm_num [tp12086]) (by norm_num [tm12086])
    (by norm_num [ep12086]) (by norm_num [em12086])
    positive12086 negative12086 tails12086.1 tails12086.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12086.1 tailGuards12086.2

theorem preserves12086 : master12086.toScalarCertificate = scalar12086 := rfl

noncomputable def tp12087 : ℝ := (1183359017 / 5000000000)
noncomputable def tm12087 : ℝ := (-((76563589 / 125000000)))
noncomputable def ep12087 : ℝ := (272071433423493 / 500000000000000000)
noncomputable def em12087 : ℝ := (6560179878724857 / 12500000000000000000)
noncomputable def bp12087 : ℝ := (5493671483388710089 / 12500000000000000000)
noncomputable def bm12087 : ℝ := (2828234093916943903 / 6250000000000000000)

theorem positive12087 :
    Eplus aL (agent12087.root+dsL) scalar12087.worldRadius world12087.frame
      agent12087.frame tp12087 ≤ -ep12087 := by
  apply positive_check (eT := (116204433533769371251 / 100000000000000000000)) (y := (3958700675252706437 / 10000000000000000000)) (u := (148567626741584832051 / 100000000000000000000))
  · norm_num [world12087, agent12087, scalar12087, tp12087, tm12087, ep12087, em12087, dsL]
  · norm_num [world12087, agent12087, scalar12087, tp12087, tm12087, ep12087, em12087, dsL]
  · norm_num [world12087, agent12087, scalar12087, tp12087, tm12087, ep12087, em12087, dsL]
  · norm_num [world12087, agent12087, scalar12087, tp12087, tm12087, ep12087, em12087, dsL]
  · norm_num [world12087, agent12087, scalar12087, tp12087, tm12087, ep12087, em12087, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12087, agent12087, tp12087, tm12087, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12087, agent12087, scalar12087, tp12087, tm12087, ep12087, em12087, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12087, agent12087, tp12087, tm12087, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12087, agent12087, scalar12087, tp12087, tm12087, ep12087, em12087, dsL]

theorem negative12087 :
    Eminus aL (agent12087.root+dsL) scalar12087.worldRadius world12087.frame
      agent12087.frame tm12087 ≤ -em12087 := by
  apply negative_check (lo := (67795845788902940363 / 100000000000000000000)) (hi := (16948961447225735091 / 25000000000000000000))
    (y := (-((73327985342514184529 / 100000000000000000000)))) (u := (12008274711501962971 / 25000000000000000000))
  · norm_num [world12087, agent12087, scalar12087, tp12087, tm12087, ep12087, em12087, dsL]
  · norm_num [world12087, agent12087, scalar12087, tp12087, tm12087, ep12087, em12087, dsL]
  · norm_num [world12087, agent12087, scalar12087, tp12087, tm12087, ep12087, em12087, dsL]
  · norm_num [world12087, agent12087, scalar12087, tp12087, tm12087, ep12087, em12087, dsL]
  · norm_num [world12087, agent12087, scalar12087, tp12087, tm12087, ep12087, em12087, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12087, agent12087, tp12087, tm12087, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12087, agent12087, tp12087, tm12087, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12087, agent12087, scalar12087, tp12087, tm12087, ep12087, em12087, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12087, agent12087, tp12087, tm12087, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12087, agent12087, scalar12087, tp12087, tm12087, ep12087, em12087, dsL]

theorem tails12087 :
    exp (-((12087:ℝ)*ep12087)) ≤ scalar12087.upperTail ∧
    exp (-((12087:ℝ)*em12087)) ≤ scalar12087.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12087:ℝ)) (by norm_num [ep12087]) ?_)
      (show bp12087^8 ≤ scalar12087.upperTail by norm_num [bp12087, scalar12087])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12087, bp12087, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12087:ℝ)) (by norm_num [em12087]) ?_)
      (show bm12087^8 ≤ scalar12087.lowerTail by norm_num [bm12087, scalar12087])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12087, bm12087, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12087 :
    agent12087.root+dsL+scalar12087.worldRadius < √(1/100/aL) ∧
    2*(agent12087.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12087, agent12087, scalar12087, tp12087, tm12087, ep12087, em12087, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12087, agent12087, scalar12087, tp12087, tm12087, ep12087, em12087, dsL]

noncomputable def master12087 : MasterCertificate 12087 world12087 agent12087 :=
  master scalar12087 dsL tp12087 tm12087 ep12087 em12087
    (by norm_num [dsL]) (by norm_num [tp12087]) (by norm_num [tm12087])
    (by norm_num [ep12087]) (by norm_num [em12087])
    positive12087 negative12087 tails12087.1 tails12087.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12087.1 tailGuards12087.2

theorem preserves12087 : master12087.toScalarCertificate = scalar12087 := rfl

noncomputable def tp12088 : ℝ := (2366819183 / 10000000000)
noncomputable def tm12088 : ℝ := (-((6125314449 / 10000000000)))
noncomputable def ep12088 : ℝ := (27208632621781773 / 50000000000000000000)
noncomputable def em12088 : ℝ := (26242015969458099 / 50000000000000000000)
noncomputable def bp12088 : ℝ := (43944404819157220453 / 100000000000000000000)
noncomputable def bm12088 : ℝ := (22623502121756498533 / 50000000000000000000)

theorem positive12088 :
    Eplus aL (agent12088.root+dsL) scalar12088.worldRadius world12088.frame
      agent12088.frame tp12088 ≤ -ep12088 := by
  apply positive_check (eT := (116204758070341186807 / 100000000000000000000)) (y := (39587657499310858029 / 100000000000000000000)) (u := (18571074192972915647 / 12500000000000000000))
  · norm_num [world12088, agent12088, scalar12088, tp12088, tm12088, ep12088, em12088, dsL]
  · norm_num [world12088, agent12088, scalar12088, tp12088, tm12088, ep12088, em12088, dsL]
  · norm_num [world12088, agent12088, scalar12088, tp12088, tm12088, ep12088, em12088, dsL]
  · norm_num [world12088, agent12088, scalar12088, tp12088, tm12088, ep12088, em12088, dsL]
  · norm_num [world12088, agent12088, scalar12088, tp12088, tm12088, ep12088, em12088, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12088, agent12088, tp12088, tm12088, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12088, agent12088, scalar12088, tp12088, tm12088, ep12088, em12088, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12088, agent12088, tp12088, tm12088, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12088, agent12088, scalar12088, tp12088, tm12088, ep12088, em12088, dsL]

theorem negative12088 :
    Eminus aL (agent12088.root+dsL) scalar12088.worldRadius world12088.frame
      agent12088.frame tm12088 ≤ -em12088 := by
  apply negative_check (lo := (67795503956175051261 / 100000000000000000000)) (hi := (33897751978087525631 / 50000000000000000000))
    (y := (-((1466552181949973397 / 2000000000000000000)))) (u := (12008319892122009169 / 25000000000000000000))
  · norm_num [world12088, agent12088, scalar12088, tp12088, tm12088, ep12088, em12088, dsL]
  · norm_num [world12088, agent12088, scalar12088, tp12088, tm12088, ep12088, em12088, dsL]
  · norm_num [world12088, agent12088, scalar12088, tp12088, tm12088, ep12088, em12088, dsL]
  · norm_num [world12088, agent12088, scalar12088, tp12088, tm12088, ep12088, em12088, dsL]
  · norm_num [world12088, agent12088, scalar12088, tp12088, tm12088, ep12088, em12088, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12088, agent12088, tp12088, tm12088, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12088, agent12088, tp12088, tm12088, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12088, agent12088, scalar12088, tp12088, tm12088, ep12088, em12088, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12088, agent12088, tp12088, tm12088, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12088, agent12088, scalar12088, tp12088, tm12088, ep12088, em12088, dsL]

theorem tails12088 :
    exp (-((12088:ℝ)*ep12088)) ≤ scalar12088.upperTail ∧
    exp (-((12088:ℝ)*em12088)) ≤ scalar12088.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12088:ℝ)) (by norm_num [ep12088]) ?_)
      (show bp12088^8 ≤ scalar12088.upperTail by norm_num [bp12088, scalar12088])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12088, bp12088, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12088:ℝ)) (by norm_num [em12088]) ?_)
      (show bm12088^8 ≤ scalar12088.lowerTail by norm_num [bm12088, scalar12088])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12088, bm12088, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12088 :
    agent12088.root+dsL+scalar12088.worldRadius < √(1/100/aL) ∧
    2*(agent12088.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12088, agent12088, scalar12088, tp12088, tm12088, ep12088, em12088, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12088, agent12088, scalar12088, tp12088, tm12088, ep12088, em12088, dsL]

noncomputable def master12088 : MasterCertificate 12088 world12088 agent12088 :=
  master scalar12088 dsL tp12088 tm12088 ep12088 em12088
    (by norm_num [dsL]) (by norm_num [tp12088]) (by norm_num [tm12088])
    (by norm_num [ep12088]) (by norm_num [em12088])
    positive12088 negative12088 tails12088.1 tails12088.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12088.1 tailGuards12088.2

theorem preserves12088 : master12088.toScalarCertificate = scalar12088 := rfl

noncomputable def tp12089 : ℝ := (473384063 / 2000000000)
noncomputable def tm12089 : ℝ := (-((76569269 / 125000000)))
noncomputable def ep12089 : ℝ := (54420241966155733 / 100000000000000000000)
noncomputable def em12089 : ℝ := (52486623112854821 / 100000000000000000000)
noncomputable def bp12089 : ℝ := (10984859806156417451 / 25000000000000000000)
noncomputable def bm12089 : ℝ := (5655283046766639987 / 12500000000000000000)

theorem positive12089 :
    Eplus aL (agent12089.root+dsL) scalar12089.worldRadius world12089.frame
      agent12089.frame tp12089 ≤ -ep12089 := by
  apply positive_check (eT := (116205082518246838447 / 100000000000000000000)) (y := (19794154398099461989 / 50000000000000000000)) (u := (148569561169560774053 / 100000000000000000000))
  · norm_num [world12089, agent12089, scalar12089, tp12089, tm12089, ep12089, em12089, dsL]
  · norm_num [world12089, agent12089, scalar12089, tp12089, tm12089, ep12089, em12089, dsL]
  · norm_num [world12089, agent12089, scalar12089, tp12089, tm12089, ep12089, em12089, dsL]
  · norm_num [world12089, agent12089, scalar12089, tp12089, tm12089, ep12089, em12089, dsL]
  · norm_num [world12089, agent12089, scalar12089, tp12089, tm12089, ep12089, em12089, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12089, agent12089, tp12089, tm12089, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12089, agent12089, scalar12089, tp12089, tm12089, ep12089, em12089, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12089, agent12089, tp12089, tm12089, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12089, agent12089, scalar12089, tp12089, tm12089, ep12089, em12089, dsL]

theorem negative12089 :
    Eminus aL (agent12089.root+dsL) scalar12089.worldRadius world12089.frame
      agent12089.frame tm12089 ≤ -em12089 := by
  apply negative_check (lo := (33897581586926173009 / 50000000000000000000)) (hi := (67795163173852346019 / 100000000000000000000))
    (y := (-((73327231882436156387 / 100000000000000000000)))) (u := (24016730378797662151 / 50000000000000000000))
  · norm_num [world12089, agent12089, scalar12089, tp12089, tm12089, ep12089, em12089, dsL]
  · norm_num [world12089, agent12089, scalar12089, tp12089, tm12089, ep12089, em12089, dsL]
  · norm_num [world12089, agent12089, scalar12089, tp12089, tm12089, ep12089, em12089, dsL]
  · norm_num [world12089, agent12089, scalar12089, tp12089, tm12089, ep12089, em12089, dsL]
  · norm_num [world12089, agent12089, scalar12089, tp12089, tm12089, ep12089, em12089, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12089, agent12089, tp12089, tm12089, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12089, agent12089, tp12089, tm12089, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12089, agent12089, scalar12089, tp12089, tm12089, ep12089, em12089, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12089, agent12089, tp12089, tm12089, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12089, agent12089, scalar12089, tp12089, tm12089, ep12089, em12089, dsL]

theorem tails12089 :
    exp (-((12089:ℝ)*ep12089)) ≤ scalar12089.upperTail ∧
    exp (-((12089:ℝ)*em12089)) ≤ scalar12089.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12089:ℝ)) (by norm_num [ep12089]) ?_)
      (show bp12089^8 ≤ scalar12089.upperTail by norm_num [bp12089, scalar12089])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12089, bp12089, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12089:ℝ)) (by norm_num [em12089]) ?_)
      (show bm12089^8 ≤ scalar12089.lowerTail by norm_num [bm12089, scalar12089])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12089, bm12089, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12089 :
    agent12089.root+dsL+scalar12089.worldRadius < √(1/100/aL) ∧
    2*(agent12089.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12089, agent12089, scalar12089, tp12089, tm12089, ep12089, em12089, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12089, agent12089, scalar12089, tp12089, tm12089, ep12089, em12089, dsL]

noncomputable def master12089 : MasterCertificate 12089 world12089 agent12089 :=
  master scalar12089 dsL tp12089 tm12089 ep12089 em12089
    (by norm_num [dsL]) (by norm_num [tp12089]) (by norm_num [tm12089])
    (by norm_num [ep12089]) (by norm_num [em12089])
    positive12089 negative12089 tails12089.1 tails12089.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12089.1 tailGuards12089.2

theorem preserves12089 : master12089.toScalarCertificate = scalar12089 := rfl

noncomputable def tp12090 : ℝ := (295877671 / 1250000000)
noncomputable def tm12090 : ℝ := (-((3062884323 / 5000000000)))
noncomputable def ep12090 : ℝ := (10884643431120211 / 20000000000000000000)
noncomputable def em12090 : ℝ := (52489212865892413 / 100000000000000000000)
noncomputable def bp12090 : ℝ := (21967237441094162453 / 50000000000000000000)
noncomputable def bm12090 : ℝ := (45237525679636531531 / 100000000000000000000)

theorem positive12090 :
    Eplus aL (agent12090.root+dsL) scalar12090.worldRadius world12090.frame
      agent12090.frame tp12090 ≤ -ep12090 := by
  apply positive_check (eT := (185928650272573279 / 160000000000000000)) (y := (9897239801555006197 / 25000000000000000000)) (u := (148570527484017425999 / 100000000000000000000))
  · norm_num [world12090, agent12090, scalar12090, tp12090, tm12090, ep12090, em12090, dsL]
  · norm_num [world12090, agent12090, scalar12090, tp12090, tm12090, ep12090, em12090, dsL]
  · norm_num [world12090, agent12090, scalar12090, tp12090, tm12090, ep12090, em12090, dsL]
  · norm_num [world12090, agent12090, scalar12090, tp12090, tm12090, ep12090, em12090, dsL]
  · norm_num [world12090, agent12090, scalar12090, tp12090, tm12090, ep12090, em12090, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12090, agent12090, tp12090, tm12090, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12090, agent12090, scalar12090, tp12090, tm12090, ep12090, em12090, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12090, agent12090, tp12090, tm12090, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12090, agent12090, scalar12090, tp12090, tm12090, ep12090, em12090, dsL]

theorem negative12090 :
    Eminus aL (agent12090.root+dsL) scalar12090.worldRadius world12090.frame
      agent12090.frame tm12090 ≤ -em12090 := by
  apply negative_check (lo := (33897411047708261463 / 50000000000000000000)) (hi := (67794822095416522927 / 100000000000000000000))
    (y := (-((2291464255313994131 / 3125000000000000000)))) (u := (24016820612798480571 / 50000000000000000000))
  · norm_num [world12090, agent12090, scalar12090, tp12090, tm12090, ep12090, em12090, dsL]
  · norm_num [world12090, agent12090, scalar12090, tp12090, tm12090, ep12090, em12090, dsL]
  · norm_num [world12090, agent12090, scalar12090, tp12090, tm12090, ep12090, em12090, dsL]
  · norm_num [world12090, agent12090, scalar12090, tp12090, tm12090, ep12090, em12090, dsL]
  · norm_num [world12090, agent12090, scalar12090, tp12090, tm12090, ep12090, em12090, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12090, agent12090, tp12090, tm12090, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12090, agent12090, tp12090, tm12090, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12090, agent12090, scalar12090, tp12090, tm12090, ep12090, em12090, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12090, agent12090, tp12090, tm12090, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12090, agent12090, scalar12090, tp12090, tm12090, ep12090, em12090, dsL]

theorem tails12090 :
    exp (-((12090:ℝ)*ep12090)) ≤ scalar12090.upperTail ∧
    exp (-((12090:ℝ)*em12090)) ≤ scalar12090.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12090:ℝ)) (by norm_num [ep12090]) ?_)
      (show bp12090^8 ≤ scalar12090.upperTail by norm_num [bp12090, scalar12090])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12090, bp12090, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12090:ℝ)) (by norm_num [em12090]) ?_)
      (show bm12090^8 ≤ scalar12090.lowerTail by norm_num [bm12090, scalar12090])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12090, bm12090, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12090 :
    agent12090.root+dsL+scalar12090.worldRadius < √(1/100/aL) ∧
    2*(agent12090.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12090, agent12090, scalar12090, tp12090, tm12090, ep12090, em12090, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12090, agent12090, scalar12090, tp12090, tm12090, ep12090, em12090, dsL]

noncomputable def master12090 : MasterCertificate 12090 world12090 agent12090 :=
  master scalar12090 dsL tp12090 tm12090 ep12090 em12090
    (by norm_num [dsL]) (by norm_num [tp12090]) (by norm_num [tm12090])
    (by norm_num [ep12090]) (by norm_num [em12090])
    positive12090 negative12090 tails12090.1 tails12090.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12090.1 tailGuards12090.2

theorem preserves12090 : master12090.toScalarCertificate = scalar12090 := rfl

noncomputable def tp12091 : ℝ := (1183561199 / 5000000000)
noncomputable def tm12091 : ℝ := (-((30629977 / 50000000)))
noncomputable def ep12091 : ℝ := (13606547749175971 / 25000000000000000000)
noncomputable def em12091 : ℝ := (10498360266450277 / 20000000000000000000)
noncomputable def bp12091 : ℝ := (43929511669101186463 / 100000000000000000000)
noncomputable def bm12091 : ℝ := (45232788068239668233 / 100000000000000000000)

theorem positive12091 :
    Eplus aL (agent12091.root+dsL) scalar12091.worldRadius world12091.frame
      agent12091.frame tp12091 ≤ -ep12091 := by
  apply positive_check (eT := (58102865094782102759 / 50000000000000000000)) (y := (39589610005734219961 / 100000000000000000000)) (u := (148571494383434814133 / 100000000000000000000))
  · norm_num [world12091, agent12091, scalar12091, tp12091, tm12091, ep12091, em12091, dsL]
  · norm_num [world12091, agent12091, scalar12091, tp12091, tm12091, ep12091, em12091, dsL]
  · norm_num [world12091, agent12091, scalar12091, tp12091, tm12091, ep12091, em12091, dsL]
  · norm_num [world12091, agent12091, scalar12091, tp12091, tm12091, ep12091, em12091, dsL]
  · norm_num [world12091, agent12091, scalar12091, tp12091, tm12091, ep12091, em12091, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12091, agent12091, tp12091, tm12091, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12091, agent12091, scalar12091, tp12091, tm12091, ep12091, em12091, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12091, agent12091, tp12091, tm12091, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12091, agent12091, scalar12091, tp12091, tm12091, ep12091, em12091, dsL]

theorem negative12091 :
    Eminus aL (agent12091.root+dsL) scalar12091.worldRadius world12091.frame
      agent12091.frame tm12091 ≤ -em12091 := by
  apply negative_check (lo := (13558896511540493623 / 20000000000000000000)) (hi := (16948620639425617029 / 25000000000000000000))
    (y := (-((36663239249461711061 / 50000000000000000000)))) (u := (48033822635132428847 / 100000000000000000000))
  · norm_num [world12091, agent12091, scalar12091, tp12091, tm12091, ep12091, em12091, dsL]
  · norm_num [world12091, agent12091, scalar12091, tp12091, tm12091, ep12091, em12091, dsL]
  · norm_num [world12091, agent12091, scalar12091, tp12091, tm12091, ep12091, em12091, dsL]
  · norm_num [world12091, agent12091, scalar12091, tp12091, tm12091, ep12091, em12091, dsL]
  · norm_num [world12091, agent12091, scalar12091, tp12091, tm12091, ep12091, em12091, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12091, agent12091, tp12091, tm12091, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12091, agent12091, tp12091, tm12091, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12091, agent12091, scalar12091, tp12091, tm12091, ep12091, em12091, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12091, agent12091, tp12091, tm12091, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12091, agent12091, scalar12091, tp12091, tm12091, ep12091, em12091, dsL]

theorem tails12091 :
    exp (-((12091:ℝ)*ep12091)) ≤ scalar12091.upperTail ∧
    exp (-((12091:ℝ)*em12091)) ≤ scalar12091.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12091:ℝ)) (by norm_num [ep12091]) ?_)
      (show bp12091^8 ≤ scalar12091.upperTail by norm_num [bp12091, scalar12091])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12091, bp12091, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12091:ℝ)) (by norm_num [em12091]) ?_)
      (show bm12091^8 ≤ scalar12091.lowerTail by norm_num [bm12091, scalar12091])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12091, bm12091, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12091 :
    agent12091.root+dsL+scalar12091.worldRadius < √(1/100/aL) ∧
    2*(agent12091.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12091, agent12091, scalar12091, tp12091, tm12091, ep12091, em12091, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12091, agent12091, scalar12091, tp12091, tm12091, ep12091, em12091, dsL]

noncomputable def master12091 : MasterCertificate 12091 world12091 agent12091 :=
  master scalar12091 dsL tp12091 tm12091 ep12091 em12091
    (by norm_num [dsL]) (by norm_num [tp12091]) (by norm_num [tm12091])
    (by norm_num [ep12091]) (by norm_num [em12091])
    positive12091 negative12091 tails12091.1 tails12091.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12091.1 tailGuards12091.2

theorem preserves12091 : master12091.toScalarCertificate = scalar12091 := rfl

noncomputable def tp12092 : ℝ := (591805821 / 2500000000)
noncomputable def tm12092 : ℝ := (-((61262221 / 100000000)))
noncomputable def ep12092 : ℝ := (54429162817637951 / 100000000000000000000)
noncomputable def em12092 : ℝ := (26247193965157851 / 50000000000000000000)
noncomputable def bp12092 : ℝ := (43924550031368930283 / 100000000000000000000)
noncomputable def bm12092 : ℝ := (45228051937529937713 / 100000000000000000000)

theorem positive12092 :
    Eplus aL (agent12092.root+dsL) scalar12092.worldRadius world12092.frame
      agent12092.frame tp12092 ≤ -ep12092 := by
  apply positive_check (eT := (116206052933779329933 / 100000000000000000000)) (y := (791805175972640601 / 2000000000000000000)) (u := (29714491661573095483 / 20000000000000000000))
  · norm_num [world12092, agent12092, scalar12092, tp12092, tm12092, ep12092, em12092, dsL]
  · norm_num [world12092, agent12092, scalar12092, tp12092, tm12092, ep12092, em12092, dsL]
  · norm_num [world12092, agent12092, scalar12092, tp12092, tm12092, ep12092, em12092, dsL]
  · norm_num [world12092, agent12092, scalar12092, tp12092, tm12092, ep12092, em12092, dsL]
  · norm_num [world12092, agent12092, scalar12092, tp12092, tm12092, ep12092, em12092, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12092, agent12092, tp12092, tm12092, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12092, agent12092, scalar12092, tp12092, tm12092, ep12092, em12092, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12092, agent12092, tp12092, tm12092, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12092, agent12092, scalar12092, tp12092, tm12092, ep12092, em12092, dsL]

theorem negative12092 :
    Eminus aL (agent12092.root+dsL) scalar12092.worldRadius world12092.frame
      agent12092.frame tm12092 ≤ -em12092 := by
  apply negative_check (lo := (13558828638535830793 / 20000000000000000000)) (hi := (33897071596339576983 / 50000000000000000000))
    (y := (-((18331525283054504323 / 25000000000000000000)))) (u := (6004250487391050227 / 12500000000000000000))
  · norm_num [world12092, agent12092, scalar12092, tp12092, tm12092, ep12092, em12092, dsL]
  · norm_num [world12092, agent12092, scalar12092, tp12092, tm12092, ep12092, em12092, dsL]
  · norm_num [world12092, agent12092, scalar12092, tp12092, tm12092, ep12092, em12092, dsL]
  · norm_num [world12092, agent12092, scalar12092, tp12092, tm12092, ep12092, em12092, dsL]
  · norm_num [world12092, agent12092, scalar12092, tp12092, tm12092, ep12092, em12092, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12092, agent12092, tp12092, tm12092, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12092, agent12092, tp12092, tm12092, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12092, agent12092, scalar12092, tp12092, tm12092, ep12092, em12092, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12092, agent12092, tp12092, tm12092, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12092, agent12092, scalar12092, tp12092, tm12092, ep12092, em12092, dsL]

theorem tails12092 :
    exp (-((12092:ℝ)*ep12092)) ≤ scalar12092.upperTail ∧
    exp (-((12092:ℝ)*em12092)) ≤ scalar12092.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12092:ℝ)) (by norm_num [ep12092]) ?_)
      (show bp12092^8 ≤ scalar12092.upperTail by norm_num [bp12092, scalar12092])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12092, bp12092, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12092:ℝ)) (by norm_num [em12092]) ?_)
      (show bm12092^8 ≤ scalar12092.lowerTail by norm_num [bm12092, scalar12092])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12092, bm12092, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12092 :
    agent12092.root+dsL+scalar12092.worldRadius < √(1/100/aL) ∧
    2*(agent12092.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12092, agent12092, scalar12092, tp12092, tm12092, ep12092, em12092, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12092, agent12092, scalar12092, tp12092, tm12092, ep12092, em12092, dsL]

noncomputable def master12092 : MasterCertificate 12092 world12092 agent12092 :=
  master scalar12092 dsL tp12092 tm12092 ep12092 em12092
    (by norm_num [dsL]) (by norm_num [tp12092]) (by norm_num [tm12092])
    (by norm_num [ep12092]) (by norm_num [em12092])
    positive12092 negative12092 tails12092.1 tails12092.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12092.1 tailGuards12092.2

theorem preserves12092 : master12092.toScalarCertificate = scalar12092 := rfl

noncomputable def tp12093 : ℝ := (473464843 / 2000000000)
noncomputable def tm12093 : ℝ := (-((6126448841 / 10000000000)))
noncomputable def ep12093 : ℝ := (13608033277736919 / 25000000000000000000)
noncomputable def em12093 : ℝ := (52496973112404763 / 100000000000000000000)
noncomputable def bp12093 : ℝ := (2744974352619820929 / 6250000000000000000)
noncomputable def bm12093 : ℝ := (45223316978254267739 / 100000000000000000000)

theorem positive12093 :
    Eplus aL (agent12093.root+dsL) scalar12093.worldRadius world12093.frame
      agent12093.frame tp12093 ≤ -ep12093 := by
  apply positive_check (eT := (232412752092987011 / 200000000000000000)) (y := (3959090893701297819 / 10000000000000000000)) (u := (5942936969503215661 / 4000000000000000000))
  · norm_num [world12093, agent12093, scalar12093, tp12093, tm12093, ep12093, em12093, dsL]
  · norm_num [world12093, agent12093, scalar12093, tp12093, tm12093, ep12093, em12093, dsL]
  · norm_num [world12093, agent12093, scalar12093, tp12093, tm12093, ep12093, em12093, dsL]
  · norm_num [world12093, agent12093, scalar12093, tp12093, tm12093, ep12093, em12093, dsL]
  · norm_num [world12093, agent12093, scalar12093, tp12093, tm12093, ep12093, em12093, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12093, agent12093, tp12093, tm12093, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12093, agent12093, scalar12093, tp12093, tm12093, ep12093, em12093, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12093, agent12093, tp12093, tm12093, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12093, agent12093, scalar12093, tp12093, tm12093, ep12093, em12093, dsL]

theorem negative12093 :
    Eminus aL (agent12093.root+dsL) scalar12093.worldRadius world12093.frame
      agent12093.frame tm12093 ≤ -em12093 := by
  apply negative_check (lo := (13558760718355827867 / 20000000000000000000)) (hi := (8474225448972392417 / 12500000000000000000))
    (y := (-((18331431282160818979 / 25000000000000000000)))) (u := (48034184509039703599 / 100000000000000000000))
  · norm_num [world12093, agent12093, scalar12093, tp12093, tm12093, ep12093, em12093, dsL]
  · norm_num [world12093, agent12093, scalar12093, tp12093, tm12093, ep12093, em12093, dsL]
  · norm_num [world12093, agent12093, scalar12093, tp12093, tm12093, ep12093, em12093, dsL]
  · norm_num [world12093, agent12093, scalar12093, tp12093, tm12093, ep12093, em12093, dsL]
  · norm_num [world12093, agent12093, scalar12093, tp12093, tm12093, ep12093, em12093, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12093, agent12093, tp12093, tm12093, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12093, agent12093, tp12093, tm12093, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12093, agent12093, scalar12093, tp12093, tm12093, ep12093, em12093, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12093, agent12093, tp12093, tm12093, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12093, agent12093, scalar12093, tp12093, tm12093, ep12093, em12093, dsL]

theorem tails12093 :
    exp (-((12093:ℝ)*ep12093)) ≤ scalar12093.upperTail ∧
    exp (-((12093:ℝ)*em12093)) ≤ scalar12093.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12093:ℝ)) (by norm_num [ep12093]) ?_)
      (show bp12093^8 ≤ scalar12093.upperTail by norm_num [bp12093, scalar12093])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12093, bp12093, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12093:ℝ)) (by norm_num [em12093]) ?_)
      (show bm12093^8 ≤ scalar12093.lowerTail by norm_num [bm12093, scalar12093])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12093, bm12093, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12093 :
    agent12093.root+dsL+scalar12093.worldRadius < √(1/100/aL) ∧
    2*(agent12093.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12093, agent12093, scalar12093, tp12093, tm12093, ep12093, em12093, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12093, agent12093, scalar12093, tp12093, tm12093, ep12093, em12093, dsL]

noncomputable def master12093 : MasterCertificate 12093 world12093 agent12093 :=
  master scalar12093 dsL tp12093 tm12093 ep12093 em12093
    (by norm_num [dsL]) (by norm_num [tp12093]) (by norm_num [tm12093])
    (by norm_num [ep12093]) (by norm_num [em12093])
    positive12093 negative12093 tails12093.1 tails12093.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12093.1 tailGuards12093.2

theorem preserves12093 : master12093.toScalarCertificate = scalar12093 := rfl

noncomputable def tp12094 : ℝ := (2367425059 / 10000000000)
noncomputable def tm12094 : ℝ := (-((1531668829 / 2500000000)))
noncomputable def ep12094 : ℝ := (435480812590783 / 800000000000000000)
noncomputable def em12094 : ℝ := (2624977828234209 / 5000000000000000000)
noncomputable def bp12094 : ℝ := (10978657675428470379 / 25000000000000000000)
noncomputable def bm12094 : ℝ := (22609291702461665309 / 50000000000000000000)

theorem positive12094 :
    Eplus aL (agent12094.root+dsL) scalar12094.worldRadius world12094.frame
      agent12094.frame tp12094 ≤ -ep12094 := by
  apply positive_check (eT := (58103349277236453301 / 50000000000000000000)) (y := (39591558362756713603 / 100000000000000000000)) (u := (148574389114778816671 / 100000000000000000000))
  · norm_num [world12094, agent12094, scalar12094, tp12094, tm12094, ep12094, em12094, dsL]
  · norm_num [world12094, agent12094, scalar12094, tp12094, tm12094, ep12094, em12094, dsL]
  · norm_num [world12094, agent12094, scalar12094, tp12094, tm12094, ep12094, em12094, dsL]
  · norm_num [world12094, agent12094, scalar12094, tp12094, tm12094, ep12094, em12094, dsL]
  · norm_num [world12094, agent12094, scalar12094, tp12094, tm12094, ep12094, em12094, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12094, agent12094, tp12094, tm12094, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12094, agent12094, scalar12094, tp12094, tm12094, ep12094, em12094, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12094, agent12094, tp12094, tm12094, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12094, agent12094, scalar12094, tp12094, tm12094, ep12094, em12094, dsL]

theorem negative12094 :
    Eminus aL (agent12094.root+dsL) scalar12094.worldRadius world12094.frame
      agent12094.frame tm12094 ≤ -em12094 := by
  apply negative_check (lo := (8474183134436831411 / 12500000000000000000)) (hi := (67793465075494651289 / 100000000000000000000))
    (y := (-((1145708563645228779 / 1562500000000000000)))) (u := (48034365624843020883 / 100000000000000000000))
  · norm_num [world12094, agent12094, scalar12094, tp12094, tm12094, ep12094, em12094, dsL]
  · norm_num [world12094, agent12094, scalar12094, tp12094, tm12094, ep12094, em12094, dsL]
  · norm_num [world12094, agent12094, scalar12094, tp12094, tm12094, ep12094, em12094, dsL]
  · norm_num [world12094, agent12094, scalar12094, tp12094, tm12094, ep12094, em12094, dsL]
  · norm_num [world12094, agent12094, scalar12094, tp12094, tm12094, ep12094, em12094, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12094, agent12094, tp12094, tm12094, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12094, agent12094, tp12094, tm12094, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12094, agent12094, scalar12094, tp12094, tm12094, ep12094, em12094, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12094, agent12094, tp12094, tm12094, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12094, agent12094, scalar12094, tp12094, tm12094, ep12094, em12094, dsL]

theorem tails12094 :
    exp (-((12094:ℝ)*ep12094)) ≤ scalar12094.upperTail ∧
    exp (-((12094:ℝ)*em12094)) ≤ scalar12094.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12094:ℝ)) (by norm_num [ep12094]) ?_)
      (show bp12094^8 ≤ scalar12094.upperTail by norm_num [bp12094, scalar12094])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12094, bp12094, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12094:ℝ)) (by norm_num [em12094]) ?_)
      (show bm12094^8 ≤ scalar12094.lowerTail by norm_num [bm12094, scalar12094])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12094, bm12094, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12094 :
    agent12094.root+dsL+scalar12094.worldRadius < √(1/100/aL) ∧
    2*(agent12094.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12094, agent12094, scalar12094, tp12094, tm12094, ep12094, em12094, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12094, agent12094, scalar12094, tp12094, tm12094, ep12094, em12094, dsL]

noncomputable def master12094 : MasterCertificate 12094 world12094 agent12094 :=
  master scalar12094 dsL tp12094 tm12094 ep12094 em12094
    (by norm_num [dsL]) (by norm_num [tp12094]) (by norm_num [tm12094])
    (by norm_num [ep12094]) (by norm_num [em12094])
    positive12094 negative12094 tails12094.1 tails12094.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12094.1 tailGuards12094.2

theorem preserves12094 : master12094.toScalarCertificate = scalar12094 := rfl

noncomputable def tp12095 : ℝ := (2367525881 / 10000000000)
noncomputable def tm12095 : ℝ := (-((95732839 / 156250000)))
noncomputable def ep12095 : ℝ := (54438068987560807 / 100000000000000000000)
noncomputable def em12095 : ℝ := (1312553476036999 / 2500000000000000000)
noncomputable def bp12095 : ℝ := (21954836346037218907 / 50000000000000000000)
noncomputable def bm12095 : ℝ := (706466417216549001 / 1562500000000000000)

theorem positive12095 :
    Eplus aL (agent12095.root+dsL) scalar12095.worldRadius world12095.frame
      agent12095.frame tp12095 ≤ -ep12095 := by
  apply positive_check (eT := (116207020936982425093 / 100000000000000000000)) (y := (7918441574932003019 / 20000000000000000000)) (u := (148575354126255303447 / 100000000000000000000))
  · norm_num [world12095, agent12095, scalar12095, tp12095, tm12095, ep12095, em12095, dsL]
  · norm_num [world12095, agent12095, scalar12095, tp12095, tm12095, ep12095, em12095, dsL]
  · norm_num [world12095, agent12095, scalar12095, tp12095, tm12095, ep12095, em12095, dsL]
  · norm_num [world12095, agent12095, scalar12095, tp12095, tm12095, ep12095, em12095, dsL]
  · norm_num [world12095, agent12095, scalar12095, tp12095, tm12095, ep12095, em12095, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12095, agent12095, tp12095, tm12095, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12095, agent12095, scalar12095, tp12095, tm12095, ep12095, em12095, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12095, agent12095, tp12095, tm12095, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12095, agent12095, scalar12095, tp12095, tm12095, ep12095, em12095, dsL]

theorem negative12095 :
    Eminus aL (agent12095.root+dsL) scalar12095.worldRadius world12095.frame
      agent12095.frame tm12095 ≤ -em12095 := by
  apply negative_check (lo := (33896563454121561547 / 50000000000000000000)) (hi := (13558625381648624619 / 20000000000000000000))
    (y := (-((73324971176903340593 / 100000000000000000000)))) (u := (48034546664974812019 / 100000000000000000000))
  · norm_num [world12095, agent12095, scalar12095, tp12095, tm12095, ep12095, em12095, dsL]
  · norm_num [world12095, agent12095, scalar12095, tp12095, tm12095, ep12095, em12095, dsL]
  · norm_num [world12095, agent12095, scalar12095, tp12095, tm12095, ep12095, em12095, dsL]
  · norm_num [world12095, agent12095, scalar12095, tp12095, tm12095, ep12095, em12095, dsL]
  · norm_num [world12095, agent12095, scalar12095, tp12095, tm12095, ep12095, em12095, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12095, agent12095, tp12095, tm12095, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12095, agent12095, tp12095, tm12095, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12095, agent12095, scalar12095, tp12095, tm12095, ep12095, em12095, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12095, agent12095, tp12095, tm12095, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12095, agent12095, scalar12095, tp12095, tm12095, ep12095, em12095, dsL]

theorem tails12095 :
    exp (-((12095:ℝ)*ep12095)) ≤ scalar12095.upperTail ∧
    exp (-((12095:ℝ)*em12095)) ≤ scalar12095.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12095:ℝ)) (by norm_num [ep12095]) ?_)
      (show bp12095^8 ≤ scalar12095.upperTail by norm_num [bp12095, scalar12095])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12095, bp12095, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12095:ℝ)) (by norm_num [em12095]) ?_)
      (show bm12095^8 ≤ scalar12095.lowerTail by norm_num [bm12095, scalar12095])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12095, bm12095, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12095 :
    agent12095.root+dsL+scalar12095.worldRadius < √(1/100/aL) ∧
    2*(agent12095.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12095, agent12095, scalar12095, tp12095, tm12095, ep12095, em12095, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12095, agent12095, scalar12095, tp12095, tm12095, ep12095, em12095, dsL]

noncomputable def master12095 : MasterCertificate 12095 world12095 agent12095 :=
  master scalar12095 dsL tp12095 tm12095 ep12095 em12095
    (by norm_num [dsL]) (by norm_num [tp12095]) (by norm_num [tm12095])
    (by norm_num [ep12095]) (by norm_num [em12095])
    positive12095 negative12095 tails12095.1 tails12095.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12095.1 tailGuards12095.2

theorem preserves12095 : master12095.toScalarCertificate = scalar12095 := rfl

noncomputable def tp12096 : ℝ := (2367626743 / 10000000000)
noncomputable def tm12096 : ℝ := (-((6127128177 / 10000000000)))
noncomputable def ep12096 : ℝ := (1701282385404449 / 3125000000000000000)
noncomputable def em12096 : ℝ := (52504721728066543 / 100000000000000000000)
noncomputable def bp12096 : ℝ := (21952357480926048829 / 50000000000000000000)
noncomputable def bm12096 : ℝ := (1130227951471227607 / 2500000000000000000)

theorem positive12096 :
    Eplus aL (agent12096.root+dsL) scalar12096.worldRadius world12096.frame
      agent12096.frame tp12096 ≤ -ep12096 := by
  apply positive_check (eT := (116207343651128924519 / 100000000000000000000)) (y := (3959285618583543929 / 10000000000000000000)) (u := (74288158680001201337 / 50000000000000000000))
  · norm_num [world12096, agent12096, scalar12096, tp12096, tm12096, ep12096, em12096, dsL]
  · norm_num [world12096, agent12096, scalar12096, tp12096, tm12096, ep12096, em12096, dsL]
  · norm_num [world12096, agent12096, scalar12096, tp12096, tm12096, ep12096, em12096, dsL]
  · norm_num [world12096, agent12096, scalar12096, tp12096, tm12096, ep12096, em12096, dsL]
  · norm_num [world12096, agent12096, scalar12096, tp12096, tm12096, ep12096, em12096, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12096, agent12096, tp12096, tm12096, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12096, agent12096, scalar12096, tp12096, tm12096, ep12096, em12096, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12096, agent12096, tp12096, tm12096, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12096, agent12096, scalar12096, tp12096, tm12096, ep12096, em12096, dsL]

theorem negative12096 :
    Eminus aL (agent12096.root+dsL) scalar12096.worldRadius world12096.frame
      agent12096.frame tm12096 ≤ -em12096 := by
  apply negative_check (lo := (6779278824700570047 / 10000000000000000000)) (hi := (67792788247005700471 / 100000000000000000000))
    (y := (-((73324591232389230971 / 100000000000000000000)))) (u := (48034729169946451611 / 100000000000000000000))
  · norm_num [world12096, agent12096, scalar12096, tp12096, tm12096, ep12096, em12096, dsL]
  · norm_num [world12096, agent12096, scalar12096, tp12096, tm12096, ep12096, em12096, dsL]
  · norm_num [world12096, agent12096, scalar12096, tp12096, tm12096, ep12096, em12096, dsL]
  · norm_num [world12096, agent12096, scalar12096, tp12096, tm12096, ep12096, em12096, dsL]
  · norm_num [world12096, agent12096, scalar12096, tp12096, tm12096, ep12096, em12096, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12096, agent12096, tp12096, tm12096, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12096, agent12096, tp12096, tm12096, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12096, agent12096, scalar12096, tp12096, tm12096, ep12096, em12096, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12096, agent12096, tp12096, tm12096, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12096, agent12096, scalar12096, tp12096, tm12096, ep12096, em12096, dsL]

theorem tails12096 :
    exp (-((12096:ℝ)*ep12096)) ≤ scalar12096.upperTail ∧
    exp (-((12096:ℝ)*em12096)) ≤ scalar12096.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12096:ℝ)) (by norm_num [ep12096]) ?_)
      (show bp12096^8 ≤ scalar12096.upperTail by norm_num [bp12096, scalar12096])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12096, bp12096, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12096:ℝ)) (by norm_num [em12096]) ?_)
      (show bm12096^8 ≤ scalar12096.lowerTail by norm_num [bm12096, scalar12096])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12096, bm12096, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12096 :
    agent12096.root+dsL+scalar12096.worldRadius < √(1/100/aL) ∧
    2*(agent12096.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12096, agent12096, scalar12096, tp12096, tm12096, ep12096, em12096, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12096, agent12096, scalar12096, tp12096, tm12096, ep12096, em12096, dsL]

noncomputable def master12096 : MasterCertificate 12096 world12096 agent12096 :=
  master scalar12096 dsL tp12096 tm12096 ep12096 em12096
    (by norm_num [dsL]) (by norm_num [tp12096]) (by norm_num [tm12096])
    (by norm_num [ep12096]) (by norm_num [em12096])
    positive12096 negative12096 tails12096.1 tails12096.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12096.1 tailGuards12096.2

theorem preserves12096 : master12096.toScalarCertificate = scalar12096 := rfl

noncomputable def tp12097 : ℝ := (2367727737 / 10000000000)
noncomputable def tm12097 : ℝ := (-((6127355321 / 10000000000)))
noncomputable def ep12097 : ℝ := (54444006281212037 / 100000000000000000000)
noncomputable def em12097 : ℝ := (52507307506371897 / 100000000000000000000)
noncomputable def bp12097 : ℝ := (43899755737883108167 / 100000000000000000000)
noncomputable def bm12097 : ℝ := (45204383506009878003 / 100000000000000000000)

theorem positive12097 :
    Eplus aL (agent12097.root+dsL) scalar12097.worldRadius world12097.frame
      agent12097.frame tp12097 ≤ -ep12097 := by
  apply positive_check (eT := (116207667375091656567 / 100000000000000000000)) (y := (9898375304660552521 / 25000000000000000000)) (u := (37144318932270840187 / 25000000000000000000))
  · norm_num [world12097, agent12097, scalar12097, tp12097, tm12097, ep12097, em12097, dsL]
  · norm_num [world12097, agent12097, scalar12097, tp12097, tm12097, ep12097, em12097, dsL]
  · norm_num [world12097, agent12097, scalar12097, tp12097, tm12097, ep12097, em12097, dsL]
  · norm_num [world12097, agent12097, scalar12097, tp12097, tm12097, ep12097, em12097, dsL]
  · norm_num [world12097, agent12097, scalar12097, tp12097, tm12097, ep12097, em12097, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12097, agent12097, tp12097, tm12097, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12097, agent12097, scalar12097, tp12097, tm12097, ep12097, em12097, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12097, agent12097, tp12097, tm12097, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12097, agent12097, scalar12097, tp12097, tm12097, ep12097, em12097, dsL]

theorem negative12097 :
    Eminus aL (agent12097.root+dsL) scalar12097.worldRadius world12097.frame
      agent12097.frame tm12097 ≤ -em12097 := by
  apply negative_check (lo := (6779244667486928861 / 10000000000000000000)) (hi := (67792446674869288611 / 100000000000000000000))
    (y := (-((18331051594142284381 / 25000000000000000000)))) (u := (4803491403475305953 / 10000000000000000000))
  · norm_num [world12097, agent12097, scalar12097, tp12097, tm12097, ep12097, em12097, dsL]
  · norm_num [world12097, agent12097, scalar12097, tp12097, tm12097, ep12097, em12097, dsL]
  · norm_num [world12097, agent12097, scalar12097, tp12097, tm12097, ep12097, em12097, dsL]
  · norm_num [world12097, agent12097, scalar12097, tp12097, tm12097, ep12097, em12097, dsL]
  · norm_num [world12097, agent12097, scalar12097, tp12097, tm12097, ep12097, em12097, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12097, agent12097, tp12097, tm12097, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12097, agent12097, tp12097, tm12097, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12097, agent12097, scalar12097, tp12097, tm12097, ep12097, em12097, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12097, agent12097, tp12097, tm12097, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12097, agent12097, scalar12097, tp12097, tm12097, ep12097, em12097, dsL]

theorem tails12097 :
    exp (-((12097:ℝ)*ep12097)) ≤ scalar12097.upperTail ∧
    exp (-((12097:ℝ)*em12097)) ≤ scalar12097.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12097:ℝ)) (by norm_num [ep12097]) ?_)
      (show bp12097^8 ≤ scalar12097.upperTail by norm_num [bp12097, scalar12097])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12097, bp12097, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12097:ℝ)) (by norm_num [em12097]) ?_)
      (show bm12097^8 ≤ scalar12097.lowerTail by norm_num [bm12097, scalar12097])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12097, bm12097, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12097 :
    agent12097.root+dsL+scalar12097.worldRadius < √(1/100/aL) ∧
    2*(agent12097.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12097, agent12097, scalar12097, tp12097, tm12097, ep12097, em12097, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12097, agent12097, scalar12097, tp12097, tm12097, ep12097, em12097, dsL]

noncomputable def master12097 : MasterCertificate 12097 world12097 agent12097 :=
  master scalar12097 dsL tp12097 tm12097 ep12097 em12097
    (by norm_num [dsL]) (by norm_num [tp12097]) (by norm_num [tm12097])
    (by norm_num [ep12097]) (by norm_num [em12097])
    positive12097 negative12097 tails12097.1 tails12097.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12097.1 tailGuards12097.2

theorem preserves12097 : master12097.toScalarCertificate = scalar12097 := rfl

noncomputable def tp12098 : ℝ := (473565737 / 2000000000)
noncomputable def tm12098 : ℝ := (-((6127582219 / 10000000000)))
noncomputable def ep12098 : ℝ := (54446974703457329 / 100000000000000000000)
noncomputable def em12098 : ℝ := (13127472967624913 / 25000000000000000000)
noncomputable def bp12098 : ℝ := (10973699440284974103 / 25000000000000000000)
noncomputable def bm12098 : ℝ := (5649956265430520529 / 12500000000000000000)

theorem positive12098 :
    Eplus aL (agent12098.root+dsL) scalar12098.worldRadius world12098.frame
      agent12098.frame tp12098 ≤ -ep12098 := by
  apply positive_check (eT := (116207990796564190633 / 100000000000000000000)) (y := (39594145955662124783 / 100000000000000000000)) (u := (148578233664871246893 / 100000000000000000000))
  · norm_num [world12098, agent12098, scalar12098, tp12098, tm12098, ep12098, em12098, dsL]
  · norm_num [world12098, agent12098, scalar12098, tp12098, tm12098, ep12098, em12098, dsL]
  · norm_num [world12098, agent12098, scalar12098, tp12098, tm12098, ep12098, em12098, dsL]
  · norm_num [world12098, agent12098, scalar12098, tp12098, tm12098, ep12098, em12098, dsL]
  · norm_num [world12098, agent12098, scalar12098, tp12098, tm12098, ep12098, em12098, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12098, agent12098, tp12098, tm12098, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12098, agent12098, scalar12098, tp12098, tm12098, ep12098, em12098, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12098, agent12098, tp12098, tm12098, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12098, agent12098, scalar12098, tp12098, tm12098, ep12098, em12098, dsL]

theorem negative12098 :
    Eminus aL (agent12098.root+dsL) scalar12098.worldRadius world12098.frame
      agent12098.frame tm12098 ≤ -em12098 := by
  apply negative_check (lo := (33896053050691894363 / 50000000000000000000)) (hi := (67792106101383788727 / 100000000000000000000))
    (y := (-((73323820069710931873 / 100000000000000000000)))) (u := (48035099597278729121 / 100000000000000000000))
  · norm_num [world12098, agent12098, scalar12098, tp12098, tm12098, ep12098, em12098, dsL]
  · norm_num [world12098, agent12098, scalar12098, tp12098, tm12098, ep12098, em12098, dsL]
  · norm_num [world12098, agent12098, scalar12098, tp12098, tm12098, ep12098, em12098, dsL]
  · norm_num [world12098, agent12098, scalar12098, tp12098, tm12098, ep12098, em12098, dsL]
  · norm_num [world12098, agent12098, scalar12098, tp12098, tm12098, ep12098, em12098, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12098, agent12098, tp12098, tm12098, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12098, agent12098, tp12098, tm12098, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12098, agent12098, scalar12098, tp12098, tm12098, ep12098, em12098, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12098, agent12098, tp12098, tm12098, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12098, agent12098, scalar12098, tp12098, tm12098, ep12098, em12098, dsL]

theorem tails12098 :
    exp (-((12098:ℝ)*ep12098)) ≤ scalar12098.upperTail ∧
    exp (-((12098:ℝ)*em12098)) ≤ scalar12098.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12098:ℝ)) (by norm_num [ep12098]) ?_)
      (show bp12098^8 ≤ scalar12098.upperTail by norm_num [bp12098, scalar12098])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12098, bp12098, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12098:ℝ)) (by norm_num [em12098]) ?_)
      (show bm12098^8 ≤ scalar12098.lowerTail by norm_num [bm12098, scalar12098])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12098, bm12098, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12098 :
    agent12098.root+dsL+scalar12098.worldRadius < √(1/100/aL) ∧
    2*(agent12098.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12098, agent12098, scalar12098, tp12098, tm12098, ep12098, em12098, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12098, agent12098, scalar12098, tp12098, tm12098, ep12098, em12098, dsL]

noncomputable def master12098 : MasterCertificate 12098 world12098 agent12098 :=
  master scalar12098 dsL tp12098 tm12098 ep12098 em12098
    (by norm_num [dsL]) (by norm_num [tp12098]) (by norm_num [tm12098])
    (by norm_num [ep12098]) (by norm_num [em12098])
    positive12098 negative12098 tails12098.1 tails12098.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12098.1 tailGuards12098.2

theorem preserves12098 : master12098.toScalarCertificate = scalar12098 := rfl

noncomputable def tp12099 : ℝ := (2367929617 / 10000000000)
noncomputable def tm12099 : ℝ := (-((3063904507 / 5000000000)))
noncomputable def ep12099 : ℝ := (5444994130160239 / 10000000000000000000)
noncomputable def em12099 : ℝ := (2100498980423973 / 4000000000000000000)
noncomputable def bp12099 : ℝ := (21944920614717026909 / 50000000000000000000)
noncomputable def bm12099 : ℝ := (45194918122915809911 / 100000000000000000000)

theorem positive12099 :
    Eplus aL (agent12099.root+dsL) scalar12099.worldRadius world12099.frame
      agent12099.frame tp12099 ≤ -ep12099 := by
  apply positive_check (eT := (58104157068381094699 / 50000000000000000000)) (y := (39594791256557713223 / 100000000000000000000)) (u := (148579192444637239673 / 100000000000000000000))
  · norm_num [world12099, agent12099, scalar12099, tp12099, tm12099, ep12099, em12099, dsL]
  · norm_num [world12099, agent12099, scalar12099, tp12099, tm12099, ep12099, em12099, dsL]
  · norm_num [world12099, agent12099, scalar12099, tp12099, tm12099, ep12099, em12099, dsL]
  · norm_num [world12099, agent12099, scalar12099, tp12099, tm12099, ep12099, em12099, dsL]
  · norm_num [world12099, agent12099, scalar12099, tp12099, tm12099, ep12099, em12099, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12099, agent12099, tp12099, tm12099, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12099, agent12099, scalar12099, tp12099, tm12099, ep12099, em12099, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12099, agent12099, tp12099, tm12099, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12099, agent12099, scalar12099, tp12099, tm12099, ep12099, em12099, dsL]

theorem negative12099 :
    Eminus aL (agent12099.root+dsL) scalar12099.worldRadius world12099.frame
      agent12099.frame tm12099 ≤ -em12099 := by
  apply negative_check (lo := (13558353182286460289 / 20000000000000000000)) (hi := (33895882955716150723 / 50000000000000000000))
    (y := (-((14664686860687239367 / 20000000000000000000)))) (u := (48035284900850429921 / 100000000000000000000))
  · norm_num [world12099, agent12099, scalar12099, tp12099, tm12099, ep12099, em12099, dsL]
  · norm_num [world12099, agent12099, scalar12099, tp12099, tm12099, ep12099, em12099, dsL]
  · norm_num [world12099, agent12099, scalar12099, tp12099, tm12099, ep12099, em12099, dsL]
  · norm_num [world12099, agent12099, scalar12099, tp12099, tm12099, ep12099, em12099, dsL]
  · norm_num [world12099, agent12099, scalar12099, tp12099, tm12099, ep12099, em12099, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12099, agent12099, tp12099, tm12099, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12099, agent12099, tp12099, tm12099, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12099, agent12099, scalar12099, tp12099, tm12099, ep12099, em12099, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12099, agent12099, tp12099, tm12099, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12099, agent12099, scalar12099, tp12099, tm12099, ep12099, em12099, dsL]

theorem tails12099 :
    exp (-((12099:ℝ)*ep12099)) ≤ scalar12099.upperTail ∧
    exp (-((12099:ℝ)*em12099)) ≤ scalar12099.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12099:ℝ)) (by norm_num [ep12099]) ?_)
      (show bp12099^8 ≤ scalar12099.upperTail by norm_num [bp12099, scalar12099])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12099, bp12099, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12099:ℝ)) (by norm_num [em12099]) ?_)
      (show bm12099^8 ≤ scalar12099.lowerTail by norm_num [bm12099, scalar12099])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12099, bm12099, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12099 :
    agent12099.root+dsL+scalar12099.worldRadius < √(1/100/aL) ∧
    2*(agent12099.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12099, agent12099, scalar12099, tp12099, tm12099, ep12099, em12099, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12099, agent12099, scalar12099, tp12099, tm12099, ep12099, em12099, dsL]

noncomputable def master12099 : MasterCertificate 12099 world12099 agent12099 :=
  master scalar12099 dsL tp12099 tm12099 ep12099 em12099
    (by norm_num [dsL]) (by norm_num [tp12099]) (by norm_num [tm12099])
    (by norm_num [ep12099]) (by norm_num [em12099])
    positive12099 negative12099 tails12099.1 tails12099.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12099.1 tailGuards12099.2

theorem preserves12099 : master12099.toScalarCertificate = scalar12099 := rfl

noncomputable def tp12100 : ℝ := (2368030469 / 10000000000)
noncomputable def tm12100 : ℝ := (-((1225607157 / 2000000000)))
noncomputable def ep12100 : ℝ := (54452906338488511 / 100000000000000000000)
noncomputable def em12100 : ℝ := (52515055714137803 / 100000000000000000000)
noncomputable def bp12100 : ℝ := (8776977193647890841 / 20000000000000000000)
noncomputable def bm12100 : ℝ := (45190187307902608199 / 100000000000000000000)

theorem positive12100 :
    Eplus aL (agent12100.root+dsL) scalar12100.worldRadius world12100.frame
      agent12100.frame tp12100 ≤ -ep12100 := by
  apply positive_check (eT := (11620863692385610089 / 10000000000000000000)) (y := (39595435755504181631 / 100000000000000000000)) (u := (5943206001562122251 / 4000000000000000000))
  · norm_num [world12100, agent12100, scalar12100, tp12100, tm12100, ep12100, em12100, dsL]
  · norm_num [world12100, agent12100, scalar12100, tp12100, tm12100, ep12100, em12100, dsL]
  · norm_num [world12100, agent12100, scalar12100, tp12100, tm12100, ep12100, em12100, dsL]
  · norm_num [world12100, agent12100, scalar12100, tp12100, tm12100, ep12100, em12100, dsL]
  · norm_num [world12100, agent12100, scalar12100, tp12100, tm12100, ep12100, em12100, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12100, agent12100, tp12100, tm12100, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12100, agent12100, scalar12100, tp12100, tm12100, ep12100, em12100, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12100, agent12100, tp12100, tm12100, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12100, agent12100, scalar12100, tp12100, tm12100, ep12100, em12100, dsL]

theorem negative12100 :
    Eminus aL (agent12100.root+dsL) scalar12100.worldRadius world12100.frame
      agent12100.frame tm12100 ≤ -em12100 := by
  apply negative_check (lo := (13558285153063668229 / 20000000000000000000)) (hi := (33895712882659170573 / 50000000000000000000))
    (y := (-((36661524839792499473 / 50000000000000000000)))) (u := (48035469656368456117 / 100000000000000000000))
  · norm_num [world12100, agent12100, scalar12100, tp12100, tm12100, ep12100, em12100, dsL]
  · norm_num [world12100, agent12100, scalar12100, tp12100, tm12100, ep12100, em12100, dsL]
  · norm_num [world12100, agent12100, scalar12100, tp12100, tm12100, ep12100, em12100, dsL]
  · norm_num [world12100, agent12100, scalar12100, tp12100, tm12100, ep12100, em12100, dsL]
  · norm_num [world12100, agent12100, scalar12100, tp12100, tm12100, ep12100, em12100, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12100, agent12100, tp12100, tm12100, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12100, agent12100, tp12100, tm12100, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12100, agent12100, scalar12100, tp12100, tm12100, ep12100, em12100, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12100, agent12100, tp12100, tm12100, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12100, agent12100, scalar12100, tp12100, tm12100, ep12100, em12100, dsL]

theorem tails12100 :
    exp (-((12100:ℝ)*ep12100)) ≤ scalar12100.upperTail ∧
    exp (-((12100:ℝ)*em12100)) ≤ scalar12100.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12100:ℝ)) (by norm_num [ep12100]) ?_)
      (show bp12100^8 ≤ scalar12100.upperTail by norm_num [bp12100, scalar12100])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12100, bp12100, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12100:ℝ)) (by norm_num [em12100]) ?_)
      (show bm12100^8 ≤ scalar12100.lowerTail by norm_num [bm12100, scalar12100])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12100, bm12100, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12100 :
    agent12100.root+dsL+scalar12100.worldRadius < √(1/100/aL) ∧
    2*(agent12100.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12100, agent12100, scalar12100, tp12100, tm12100, ep12100, em12100, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12100, agent12100, scalar12100, tp12100, tm12100, ep12100, em12100, dsL]

noncomputable def master12100 : MasterCertificate 12100 world12100 agent12100 :=
  master scalar12100 dsL tp12100 tm12100 ep12100 em12100
    (by norm_num [dsL]) (by norm_num [tp12100]) (by norm_num [tm12100])
    (by norm_num [ep12100]) (by norm_num [em12100])
    positive12100 negative12100 tails12100.1 tails12100.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12100.1 tailGuards12100.2

theorem preserves12100 : master12100.toScalarCertificate = scalar12100 := rfl

noncomputable def tp12101 : ℝ := (2368131321 / 10000000000)
noncomputable def tm12101 : ℝ := (-((1532065571 / 2500000000)))
noncomputable def ep12101 : ℝ := (27227935052972901 / 50000000000000000000)
noncomputable def em12101 : ℝ := (6564704460516001 / 12500000000000000000)
noncomputable def bp12101 : ℝ := (5484991472976258619 / 12500000000000000000)
noncomputable def bm12101 : ℝ := (45185457539622801219 / 100000000000000000000)

theorem positive12101 :
    Eplus aL (agent12101.root+dsL) scalar12101.worldRadius world12101.frame
      agent12101.frame tp12101 ≤ -ep12101 := by
  apply positive_check (eT := (58104479873809962909 / 50000000000000000000)) (y := (39596080840134051989 / 100000000000000000000)) (u := (148581108509855467113 / 100000000000000000000))
  · norm_num [world12101, agent12101, scalar12101, tp12101, tm12101, ep12101, em12101, dsL]
  · norm_num [world12101, agent12101, scalar12101, tp12101, tm12101, ep12101, em12101, dsL]
  · norm_num [world12101, agent12101, scalar12101, tp12101, tm12101, ep12101, em12101, dsL]
  · norm_num [world12101, agent12101, scalar12101, tp12101, tm12101, ep12101, em12101, dsL]
  · norm_num [world12101, agent12101, scalar12101, tp12101, tm12101, ep12101, em12101, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12101, agent12101, tp12101, tm12101, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12101, agent12101, scalar12101, tp12101, tm12101, ep12101, em12101, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12101, agent12101, tp12101, tm12101, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12101, agent12101, scalar12101, tp12101, tm12101, ep12101, em12101, dsL]

theorem negative12101 :
    Eminus aL (agent12101.root+dsL) scalar12101.worldRadius world12101.frame
      agent12101.frame tm12101 ≤ -em12101 := by
  apply negative_check (lo := (16947771682371058193 / 25000000000000000000)) (hi := (67791086729484232773 / 100000000000000000000))
    (y := (-((73322663226782294077 / 100000000000000000000)))) (u := (48035655291145930769 / 100000000000000000000))
  · norm_num [world12101, agent12101, scalar12101, tp12101, tm12101, ep12101, em12101, dsL]
  · norm_num [world12101, agent12101, scalar12101, tp12101, tm12101, ep12101, em12101, dsL]
  · norm_num [world12101, agent12101, scalar12101, tp12101, tm12101, ep12101, em12101, dsL]
  · norm_num [world12101, agent12101, scalar12101, tp12101, tm12101, ep12101, em12101, dsL]
  · norm_num [world12101, agent12101, scalar12101, tp12101, tm12101, ep12101, em12101, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12101, agent12101, tp12101, tm12101, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12101, agent12101, tp12101, tm12101, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12101, agent12101, scalar12101, tp12101, tm12101, ep12101, em12101, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12101, agent12101, tp12101, tm12101, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12101, agent12101, scalar12101, tp12101, tm12101, ep12101, em12101, dsL]

theorem tails12101 :
    exp (-((12101:ℝ)*ep12101)) ≤ scalar12101.upperTail ∧
    exp (-((12101:ℝ)*em12101)) ≤ scalar12101.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12101:ℝ)) (by norm_num [ep12101]) ?_)
      (show bp12101^8 ≤ scalar12101.upperTail by norm_num [bp12101, scalar12101])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12101, bp12101, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12101:ℝ)) (by norm_num [em12101]) ?_)
      (show bm12101^8 ≤ scalar12101.lowerTail by norm_num [bm12101, scalar12101])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12101, bm12101, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12101 :
    agent12101.root+dsL+scalar12101.worldRadius < √(1/100/aL) ∧
    2*(agent12101.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12101, agent12101, scalar12101, tp12101, tm12101, ep12101, em12101, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12101, agent12101, scalar12101, tp12101, tm12101, ep12101, em12101, dsL]

noncomputable def master12101 : MasterCertificate 12101 world12101 agent12101 :=
  master scalar12101 dsL tp12101 tm12101 ep12101 em12101
    (by norm_num [dsL]) (by norm_num [tp12101]) (by norm_num [tm12101])
    (by norm_num [ep12101]) (by norm_num [em12101])
    positive12101 negative12101 tails12101.1 tails12101.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12101.1 tailGuards12101.2

theorem preserves12101 : master12101.toScalarCertificate = scalar12101 := rfl

noncomputable def tp12102 : ℝ := (1184116031 / 5000000000)
noncomputable def tm12102 : ℝ := (-((6128488781 / 10000000000)))
noncomputable def ep12102 : ℝ := (544588321611209 / 1000000000000000000)
noncomputable def em12102 : ℝ := (52520214061090983 / 100000000000000000000)
noncomputable def bp12102 : ℝ := (43874978970046474993 / 100000000000000000000)
noncomputable def bm12102 : ℝ := (11295182265938497119 / 25000000000000000000)

theorem positive12102 :
    Eplus aL (agent12102.root+dsL) scalar12102.worldRadius world12102.frame
      agent12102.frame tp12102 ≤ -ep12102 := by
  apply positive_check (eT := (116209281789807056593 / 100000000000000000000)) (y := (3959672472369812479 / 10000000000000000000)) (u := (148582065202272468557 / 100000000000000000000))
  · norm_num [world12102, agent12102, scalar12102, tp12102, tm12102, ep12102, em12102, dsL]
  · norm_num [world12102, agent12102, scalar12102, tp12102, tm12102, ep12102, em12102, dsL]
  · norm_num [world12102, agent12102, scalar12102, tp12102, tm12102, ep12102, em12102, dsL]
  · norm_num [world12102, agent12102, scalar12102, tp12102, tm12102, ep12102, em12102, dsL]
  · norm_num [world12102, agent12102, scalar12102, tp12102, tm12102, ep12102, em12102, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12102, agent12102, tp12102, tm12102, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12102, agent12102, scalar12102, tp12102, tm12102, ep12102, em12102, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12102, agent12102, tp12102, tm12102, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12102, agent12102, scalar12102, tp12102, tm12102, ep12102, em12102, dsL]

theorem negative12102 :
    Eminus aL (agent12102.root+dsL) scalar12102.worldRadius world12102.frame
      agent12102.frame tm12102 ≤ -em12102 := by
  apply negative_check (lo := (67790747642824136593 / 100000000000000000000)) (hi := (33895373821412068297 / 50000000000000000000))
    (y := (-((73322278426250300173 / 100000000000000000000)))) (u := (48035840132958673767 / 100000000000000000000))
  · norm_num [world12102, agent12102, scalar12102, tp12102, tm12102, ep12102, em12102, dsL]
  · norm_num [world12102, agent12102, scalar12102, tp12102, tm12102, ep12102, em12102, dsL]
  · norm_num [world12102, agent12102, scalar12102, tp12102, tm12102, ep12102, em12102, dsL]
  · norm_num [world12102, agent12102, scalar12102, tp12102, tm12102, ep12102, em12102, dsL]
  · norm_num [world12102, agent12102, scalar12102, tp12102, tm12102, ep12102, em12102, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12102, agent12102, tp12102, tm12102, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12102, agent12102, tp12102, tm12102, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12102, agent12102, scalar12102, tp12102, tm12102, ep12102, em12102, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12102, agent12102, tp12102, tm12102, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12102, agent12102, scalar12102, tp12102, tm12102, ep12102, em12102, dsL]

theorem tails12102 :
    exp (-((12102:ℝ)*ep12102)) ≤ scalar12102.upperTail ∧
    exp (-((12102:ℝ)*em12102)) ≤ scalar12102.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12102:ℝ)) (by norm_num [ep12102]) ?_)
      (show bp12102^8 ≤ scalar12102.upperTail by norm_num [bp12102, scalar12102])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12102, bp12102, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12102:ℝ)) (by norm_num [em12102]) ?_)
      (show bm12102^8 ≤ scalar12102.lowerTail by norm_num [bm12102, scalar12102])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12102, bm12102, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12102 :
    agent12102.root+dsL+scalar12102.worldRadius < √(1/100/aL) ∧
    2*(agent12102.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12102, agent12102, scalar12102, tp12102, tm12102, ep12102, em12102, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12102, agent12102, scalar12102, tp12102, tm12102, ep12102, em12102, dsL]

noncomputable def master12102 : MasterCertificate 12102 world12102 agent12102 :=
  master scalar12102 dsL tp12102 tm12102 ep12102 em12102
    (by norm_num [dsL]) (by norm_num [tp12102]) (by norm_num [tm12102])
    (by norm_num [ep12102]) (by norm_num [em12102])
    positive12102 negative12102 tails12102.1 tails12102.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12102.1 tailGuards12102.2

theorem preserves12102 : master12102.toScalarCertificate = scalar12102 := rfl

noncomputable def tp12103 : ℝ := (236833273 / 1000000000)
noncomputable def tm12103 : ℝ := (-((61287151 / 100000000)))
noncomputable def ep12103 : ℝ := (54461791730249043 / 100000000000000000000)
noncomputable def em12103 : ℝ := (52522790140925881 / 100000000000000000000)
noncomputable def bp12103 : ℝ := (21935014020219566119 / 50000000000000000000)
noncomputable def bm12103 : ℝ := (2823500147592885357 / 6250000000000000000)

theorem positive12103 :
    Eplus aL (agent12103.root+dsL) scalar12103.worldRadius world12103.frame
      agent12103.frame tp12103 ≤ -ep12103 := by
  apply positive_check (eT := (14526200416320005187 / 12500000000000000000)) (y := (1583894717078733401 / 4000000000000000000)) (u := (9286438805628018731 / 6250000000000000000))
  · norm_num [world12103, agent12103, scalar12103, tp12103, tm12103, ep12103, em12103, dsL]
  · norm_num [world12103, agent12103, scalar12103, tp12103, tm12103, ep12103, em12103, dsL]
  · norm_num [world12103, agent12103, scalar12103, tp12103, tm12103, ep12103, em12103, dsL]
  · norm_num [world12103, agent12103, scalar12103, tp12103, tm12103, ep12103, em12103, dsL]
  · norm_num [world12103, agent12103, scalar12103, tp12103, tm12103, ep12103, em12103, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12103, agent12103, tp12103, tm12103, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12103, agent12103, scalar12103, tp12103, tm12103, ep12103, em12103, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12103, agent12103, tp12103, tm12103, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12103, agent12103, scalar12103, tp12103, tm12103, ep12103, em12103, dsL]

theorem negative12103 :
    Eminus aL (agent12103.root+dsL) scalar12103.worldRadius world12103.frame
      agent12103.frame tm12103 ≤ -em12103 := by
  apply negative_check (lo := (67790409262168056137 / 100000000000000000000)) (hi := (33895204631084028069 / 50000000000000000000))
    (y := (-((36660946289361135151 / 50000000000000000000)))) (u := (6004503184802246297 / 12500000000000000000))
  · norm_num [world12103, agent12103, scalar12103, tp12103, tm12103, ep12103, em12103, dsL]
  · norm_num [world12103, agent12103, scalar12103, tp12103, tm12103, ep12103, em12103, dsL]
  · norm_num [world12103, agent12103, scalar12103, tp12103, tm12103, ep12103, em12103, dsL]
  · norm_num [world12103, agent12103, scalar12103, tp12103, tm12103, ep12103, em12103, dsL]
  · norm_num [world12103, agent12103, scalar12103, tp12103, tm12103, ep12103, em12103, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12103, agent12103, tp12103, tm12103, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12103, agent12103, tp12103, tm12103, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12103, agent12103, scalar12103, tp12103, tm12103, ep12103, em12103, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12103, agent12103, tp12103, tm12103, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12103, agent12103, scalar12103, tp12103, tm12103, ep12103, em12103, dsL]

theorem tails12103 :
    exp (-((12103:ℝ)*ep12103)) ≤ scalar12103.upperTail ∧
    exp (-((12103:ℝ)*em12103)) ≤ scalar12103.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12103:ℝ)) (by norm_num [ep12103]) ?_)
      (show bp12103^8 ≤ scalar12103.upperTail by norm_num [bp12103, scalar12103])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12103, bp12103, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12103:ℝ)) (by norm_num [em12103]) ?_)
      (show bm12103^8 ≤ scalar12103.lowerTail by norm_num [bm12103, scalar12103])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12103, bm12103, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12103 :
    agent12103.root+dsL+scalar12103.worldRadius < √(1/100/aL) ∧
    2*(agent12103.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12103, agent12103, scalar12103, tp12103, tm12103, ep12103, em12103, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12103, agent12103, scalar12103, tp12103, tm12103, ep12103, em12103, dsL]

noncomputable def master12103 : MasterCertificate 12103 world12103 agent12103 :=
  master scalar12103 dsL tp12103 tm12103 ep12103 em12103
    (by norm_num [dsL]) (by norm_num [tp12103]) (by norm_num [tm12103])
    (by norm_num [ep12103]) (by norm_num [em12103])
    positive12103 negative12103 tails12103.1 tails12103.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12103.1 tailGuards12103.2

theorem preserves12103 : master12103.toScalarCertificate = scalar12103 := rfl

noncomputable def tp12104 : ℝ := (1184216709 / 5000000000)
noncomputable def tm12104 : ℝ := (-((612894113 / 1000000000)))
noncomputable def ep12104 : ℝ := (27232375299308079 / 50000000000000000000)
noncomputable def em12104 : ℝ := (52525365547552799 / 100000000000000000000)
noncomputable def bp12104 : ℝ := (43865077810029164629 / 100000000000000000000)
noncomputable def bm12104 : ℝ := (4517127632290106201 / 10000000000000000000)

theorem positive12104 :
    Eplus aL (agent12104.root+dsL) scalar12104.worldRadius world12104.frame
      agent12104.frame tp12104 ≤ -ep12104 := by
  apply positive_check (eT := (23241985011087263641 / 20000000000000000000)) (y := (989950301924887427 / 2500000000000000000)) (u := (148583977990700299889 / 100000000000000000000))
  · norm_num [world12104, agent12104, scalar12104, tp12104, tm12104, ep12104, em12104, dsL]
  · norm_num [world12104, agent12104, scalar12104, tp12104, tm12104, ep12104, em12104, dsL]
  · norm_num [world12104, agent12104, scalar12104, tp12104, tm12104, ep12104, em12104, dsL]
  · norm_num [world12104, agent12104, scalar12104, tp12104, tm12104, ep12104, em12104, dsL]
  · norm_num [world12104, agent12104, scalar12104, tp12104, tm12104, ep12104, em12104, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12104, agent12104, tp12104, tm12104, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12104, agent12104, scalar12104, tp12104, tm12104, ep12104, em12104, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12104, agent12104, tp12104, tm12104, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12104, agent12104, scalar12104, tp12104, tm12104, ep12104, em12104, dsL]

theorem negative12104 :
    Eminus aL (agent12104.root+dsL) scalar12104.worldRadius world12104.frame
      agent12104.frame tm12104 ≤ -em12104 := by
  apply negative_check (lo := (4236879504045279081 / 6250000000000000000)) (hi := (67790072064724465297 / 100000000000000000000))
    (y := (-((18330376352424915209 / 25000000000000000000)))) (u := (48036211459388345721 / 100000000000000000000))
  · norm_num [world12104, agent12104, scalar12104, tp12104, tm12104, ep12104, em12104, dsL]
  · norm_num [world12104, agent12104, scalar12104, tp12104, tm12104, ep12104, em12104, dsL]
  · norm_num [world12104, agent12104, scalar12104, tp12104, tm12104, ep12104, em12104, dsL]
  · norm_num [world12104, agent12104, scalar12104, tp12104, tm12104, ep12104, em12104, dsL]
  · norm_num [world12104, agent12104, scalar12104, tp12104, tm12104, ep12104, em12104, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12104, agent12104, tp12104, tm12104, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12104, agent12104, tp12104, tm12104, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12104, agent12104, scalar12104, tp12104, tm12104, ep12104, em12104, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12104, agent12104, tp12104, tm12104, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12104, agent12104, scalar12104, tp12104, tm12104, ep12104, em12104, dsL]

theorem tails12104 :
    exp (-((12104:ℝ)*ep12104)) ≤ scalar12104.upperTail ∧
    exp (-((12104:ℝ)*em12104)) ≤ scalar12104.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12104:ℝ)) (by norm_num [ep12104]) ?_)
      (show bp12104^8 ≤ scalar12104.upperTail by norm_num [bp12104, scalar12104])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12104, bp12104, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12104:ℝ)) (by norm_num [em12104]) ?_)
      (show bm12104^8 ≤ scalar12104.lowerTail by norm_num [bm12104, scalar12104])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12104, bm12104, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12104 :
    agent12104.root+dsL+scalar12104.worldRadius < √(1/100/aL) ∧
    2*(agent12104.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12104, agent12104, scalar12104, tp12104, tm12104, ep12104, em12104, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12104, agent12104, scalar12104, tp12104, tm12104, ep12104, em12104, dsL]

noncomputable def master12104 : MasterCertificate 12104 world12104 agent12104 :=
  master scalar12104 dsL tp12104 tm12104 ep12104 em12104
    (by norm_num [dsL]) (by norm_num [tp12104]) (by norm_num [tm12104])
    (by norm_num [ep12104]) (by norm_num [em12104])
    positive12104 negative12104 tails12104.1 tails12104.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12104.1 tailGuards12104.2

theorem preserves12104 : master12104.toScalarCertificate = scalar12104 := rfl

noncomputable def tp12105 : ℝ := (236853397 / 1000000000)
noncomputable def tm12105 : ℝ := (-((6129167197 / 10000000000)))
noncomputable def ep12105 : ℝ := (340423170675007 / 625000000000000000)
noncomputable def em12105 : ℝ := (52527938940623757 / 100000000000000000000)
noncomputable def bp12105 : ℝ := (43860129246582169943 / 100000000000000000000)
noncomputable def bm12105 : ℝ := (361332414912296321 / 800000000000000000)

theorem positive12105 :
    Eplus aL (agent12105.root+dsL) scalar12105.worldRadius world12105.frame
      agent12105.frame tp12105 ≤ -ep12105 := by
  apply positive_check (eT := (116210245814511573817 / 100000000000000000000)) (y := (39598654519702718183 / 100000000000000000000)) (u := (74292466280348639767 / 50000000000000000000))
  · norm_num [world12105, agent12105, scalar12105, tp12105, tm12105, ep12105, em12105, dsL]
  · norm_num [world12105, agent12105, scalar12105, tp12105, tm12105, ep12105, em12105, dsL]
  · norm_num [world12105, agent12105, scalar12105, tp12105, tm12105, ep12105, em12105, dsL]
  · norm_num [world12105, agent12105, scalar12105, tp12105, tm12105, ep12105, em12105, dsL]
  · norm_num [world12105, agent12105, scalar12105, tp12105, tm12105, ep12105, em12105, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12105, agent12105, tp12105, tm12105, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12105, agent12105, scalar12105, tp12105, tm12105, ep12105, em12105, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12105, agent12105, tp12105, tm12105, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12105, agent12105, scalar12105, tp12105, tm12105, ep12105, em12105, dsL]

theorem negative12105 :
    Eminus aL (agent12105.root+dsL) scalar12105.worldRadius world12105.frame
      agent12105.frame tm12105 ≤ -em12105 := by
  apply negative_check (lo := (13557946929747602003 / 20000000000000000000)) (hi := (2118429207773062813 / 3125000000000000000))
    (y := (-((36660559861006897691 / 50000000000000000000)))) (u := (48036396729497982641 / 100000000000000000000))
  · norm_num [world12105, agent12105, scalar12105, tp12105, tm12105, ep12105, em12105, dsL]
  · norm_num [world12105, agent12105, scalar12105, tp12105, tm12105, ep12105, em12105, dsL]
  · norm_num [world12105, agent12105, scalar12105, tp12105, tm12105, ep12105, em12105, dsL]
  · norm_num [world12105, agent12105, scalar12105, tp12105, tm12105, ep12105, em12105, dsL]
  · norm_num [world12105, agent12105, scalar12105, tp12105, tm12105, ep12105, em12105, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12105, agent12105, tp12105, tm12105, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12105, agent12105, tp12105, tm12105, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12105, agent12105, scalar12105, tp12105, tm12105, ep12105, em12105, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12105, agent12105, tp12105, tm12105, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12105, agent12105, scalar12105, tp12105, tm12105, ep12105, em12105, dsL]

theorem tails12105 :
    exp (-((12105:ℝ)*ep12105)) ≤ scalar12105.upperTail ∧
    exp (-((12105:ℝ)*em12105)) ≤ scalar12105.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12105:ℝ)) (by norm_num [ep12105]) ?_)
      (show bp12105^8 ≤ scalar12105.upperTail by norm_num [bp12105, scalar12105])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12105, bp12105, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12105:ℝ)) (by norm_num [em12105]) ?_)
      (show bm12105^8 ≤ scalar12105.lowerTail by norm_num [bm12105, scalar12105])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12105, bm12105, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12105 :
    agent12105.root+dsL+scalar12105.worldRadius < √(1/100/aL) ∧
    2*(agent12105.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12105, agent12105, scalar12105, tp12105, tm12105, ep12105, em12105, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12105, agent12105, scalar12105, tp12105, tm12105, ep12105, em12105, dsL]

noncomputable def master12105 : MasterCertificate 12105 world12105 agent12105 :=
  master scalar12105 dsL tp12105 tm12105 ep12105 em12105
    (by norm_num [dsL]) (by norm_num [tp12105]) (by norm_num [tm12105])
    (by norm_num [ep12105]) (by norm_num [em12105])
    positive12105 negative12105 tails12105.1 tails12105.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12105.1 tailGuards12105.2

theorem preserves12105 : master12105.toScalarCertificate = scalar12105 := rfl

noncomputable def tp12106 : ℝ := (94745381 / 400000000)
noncomputable def tm12106 : ℝ := (-((6129393107 / 10000000000)))
noncomputable def ep12106 : ℝ := (5447066235110951 / 10000000000000000000)
noncomputable def em12106 : ℝ := (26265255386318569 / 50000000000000000000)
noncomputable def bp12106 : ℝ := (8771036404607328423 / 20000000000000000000)
noncomputable def bm12106 : ℝ := (9032365735120061513 / 20000000000000000000)

theorem positive12106 :
    Eplus aL (agent12106.root+dsL) scalar12106.worldRadius world12106.frame
      agent12106.frame tp12106 ≤ -ep12106 := by
  apply positive_check (eT := (907895051815843811 / 781250000000000000)) (y := (63358876329323547 / 160000000000000000)) (u := (148585888241440005349 / 100000000000000000000))
  · norm_num [world12106, agent12106, scalar12106, tp12106, tm12106, ep12106, em12106, dsL]
  · norm_num [world12106, agent12106, scalar12106, tp12106, tm12106, ep12106, em12106, dsL]
  · norm_num [world12106, agent12106, scalar12106, tp12106, tm12106, ep12106, em12106, dsL]
  · norm_num [world12106, agent12106, scalar12106, tp12106, tm12106, ep12106, em12106, dsL]
  · norm_num [world12106, agent12106, scalar12106, tp12106, tm12106, ep12106, em12106, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12106, agent12106, tp12106, tm12106, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12106, agent12106, scalar12106, tp12106, tm12106, ep12106, em12106, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12106, agent12106, tp12106, tm12106, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12106, agent12106, scalar12106, tp12106, tm12106, ep12106, em12106, dsL]

theorem negative12106 :
    Eminus aL (agent12106.root+dsL) scalar12106.worldRadius world12106.frame
      agent12106.frame tm12106 ≤ -em12106 := by
  apply negative_check (lo := (8473674731037195983 / 12500000000000000000)) (hi := (13557879569659513573 / 20000000000000000000))
    (y := (-((9165091718144377379 / 12500000000000000000)))) (u := (9607316427846193521 / 20000000000000000000))
  · norm_num [world12106, agent12106, scalar12106, tp12106, tm12106, ep12106, em12106, dsL]
  · norm_num [world12106, agent12106, scalar12106, tp12106, tm12106, ep12106, em12106, dsL]
  · norm_num [world12106, agent12106, scalar12106, tp12106, tm12106, ep12106, em12106, dsL]
  · norm_num [world12106, agent12106, scalar12106, tp12106, tm12106, ep12106, em12106, dsL]
  · norm_num [world12106, agent12106, scalar12106, tp12106, tm12106, ep12106, em12106, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12106, agent12106, tp12106, tm12106, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12106, agent12106, tp12106, tm12106, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12106, agent12106, scalar12106, tp12106, tm12106, ep12106, em12106, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12106, agent12106, tp12106, tm12106, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12106, agent12106, scalar12106, tp12106, tm12106, ep12106, em12106, dsL]

theorem tails12106 :
    exp (-((12106:ℝ)*ep12106)) ≤ scalar12106.upperTail ∧
    exp (-((12106:ℝ)*em12106)) ≤ scalar12106.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12106:ℝ)) (by norm_num [ep12106]) ?_)
      (show bp12106^8 ≤ scalar12106.upperTail by norm_num [bp12106, scalar12106])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12106, bp12106, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12106:ℝ)) (by norm_num [em12106]) ?_)
      (show bm12106^8 ≤ scalar12106.lowerTail by norm_num [bm12106, scalar12106])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12106, bm12106, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12106 :
    agent12106.root+dsL+scalar12106.worldRadius < √(1/100/aL) ∧
    2*(agent12106.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12106, agent12106, scalar12106, tp12106, tm12106, ep12106, em12106, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12106, agent12106, scalar12106, tp12106, tm12106, ep12106, em12106, dsL]

noncomputable def master12106 : MasterCertificate 12106 world12106 agent12106 :=
  master scalar12106 dsL tp12106 tm12106 ep12106 em12106
    (by norm_num [dsL]) (by norm_num [tp12106]) (by norm_num [tm12106])
    (by norm_num [ep12106]) (by norm_num [em12106])
    positive12106 negative12106 tails12106.1 tails12106.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12106.1 tailGuards12106.2

theorem preserves12106 : master12106.toScalarCertificate = scalar12106 := rfl

noncomputable def tp12107 : ℝ := (2368735033 / 10000000000)
noncomputable def tm12107 : ℝ := (-((3064809443 / 5000000000)))
noncomputable def ep12107 : ℝ := (27236807861701623 / 50000000000000000000)
noncomputable def em12107 : ℝ := (3283317564989851 / 6250000000000000000)
noncomputable def bp12107 : ℝ := (43850236142350661051 / 100000000000000000000)
noncomputable def bm12107 : ℝ := (22578553380063184621 / 50000000000000000000)

theorem positive12107 :
    Eplus aL (agent12107.root+dsL) scalar12107.worldRadius world12107.frame
      agent12107.frame tp12107 ≤ -ep12107 := by
  apply positive_check (eT := (3631590223143951087 / 3125000000000000000)) (y := (19799970367338343053 / 50000000000000000000)) (u := (37146710923659888621 / 25000000000000000000))
  · norm_num [world12107, agent12107, scalar12107, tp12107, tm12107, ep12107, em12107, dsL]
  · norm_num [world12107, agent12107, scalar12107, tp12107, tm12107, ep12107, em12107, dsL]
  · norm_num [world12107, agent12107, scalar12107, tp12107, tm12107, ep12107, em12107, dsL]
  · norm_num [world12107, agent12107, scalar12107, tp12107, tm12107, ep12107, em12107, dsL]
  · norm_num [world12107, agent12107, scalar12107, tp12107, tm12107, ep12107, em12107, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12107, agent12107, tp12107, tm12107, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12107, agent12107, scalar12107, tp12107, tm12107, ep12107, em12107, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12107, agent12107, tp12107, tm12107, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12107, agent12107, scalar12107, tp12107, tm12107, ep12107, em12107, dsL]

theorem negative12107 :
    Eminus aL (agent12107.root+dsL) scalar12107.worldRadius world12107.frame
      agent12107.frame tm12107 ≤ -em12107 := by
  apply negative_check (lo := (67789061551629332189 / 100000000000000000000)) (hi := (6778906155162933219 / 10000000000000000000))
    (y := (-((2932813909316694881 / 4000000000000000000)))) (u := (24018383783337229237 / 50000000000000000000))
  · norm_num [world12107, agent12107, scalar12107, tp12107, tm12107, ep12107, em12107, dsL]
  · norm_num [world12107, agent12107, scalar12107, tp12107, tm12107, ep12107, em12107, dsL]
  · norm_num [world12107, agent12107, scalar12107, tp12107, tm12107, ep12107, em12107, dsL]
  · norm_num [world12107, agent12107, scalar12107, tp12107, tm12107, ep12107, em12107, dsL]
  · norm_num [world12107, agent12107, scalar12107, tp12107, tm12107, ep12107, em12107, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12107, agent12107, tp12107, tm12107, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12107, agent12107, tp12107, tm12107, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12107, agent12107, scalar12107, tp12107, tm12107, ep12107, em12107, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12107, agent12107, tp12107, tm12107, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12107, agent12107, scalar12107, tp12107, tm12107, ep12107, em12107, dsL]

theorem tails12107 :
    exp (-((12107:ℝ)*ep12107)) ≤ scalar12107.upperTail ∧
    exp (-((12107:ℝ)*em12107)) ≤ scalar12107.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12107:ℝ)) (by norm_num [ep12107]) ?_)
      (show bp12107^8 ≤ scalar12107.upperTail by norm_num [bp12107, scalar12107])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12107, bp12107, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12107:ℝ)) (by norm_num [em12107]) ?_)
      (show bm12107^8 ≤ scalar12107.lowerTail by norm_num [bm12107, scalar12107])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12107, bm12107, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12107 :
    agent12107.root+dsL+scalar12107.worldRadius < √(1/100/aL) ∧
    2*(agent12107.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12107, agent12107, scalar12107, tp12107, tm12107, ep12107, em12107, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12107, agent12107, scalar12107, tp12107, tm12107, ep12107, em12107, dsL]

noncomputable def master12107 : MasterCertificate 12107 world12107 agent12107 :=
  master scalar12107 dsL tp12107 tm12107 ep12107 em12107
    (by norm_num [dsL]) (by norm_num [tp12107]) (by norm_num [tm12107])
    (by norm_num [ep12107]) (by norm_num [em12107])
    positive12107 negative12107 tails12107.1 tails12107.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12107.1 tailGuards12107.2

theorem preserves12107 : master12107.toScalarCertificate = scalar12107 := rfl

noncomputable def tp12108 : ℝ := (2368835457 / 10000000000)
noncomputable def tm12108 : ℝ := (-((191557643 / 312500000)))
noncomputable def ep12108 : ℝ := (1361914189536719 / 2500000000000000000)
noncomputable def em12108 : ℝ := (10507129980733269 / 20000000000000000000)
noncomputable def bp12108 : ℝ := (43845291500559944353 / 100000000000000000000)
noncomputable def bm12108 : ℝ := (5644048250907286861 / 12500000000000000000)

theorem positive12108 :
    Eplus aL (agent12108.root+dsL) scalar12108.worldRadius world12108.frame
      agent12108.frame tp12108 ≤ -ep12108 := by
  apply positive_check (eT := (4648448282654817851 / 4000000000000000000)) (y := (1980029138989316807 / 5000000000000000000)) (u := (37146949423066405883 / 25000000000000000000))
  · norm_num [world12108, agent12108, scalar12108, tp12108, tm12108, ep12108, em12108, dsL]
  · norm_num [world12108, agent12108, scalar12108, tp12108, tm12108, ep12108, em12108, dsL]
  · norm_num [world12108, agent12108, scalar12108, tp12108, tm12108, ep12108, em12108, dsL]
  · norm_num [world12108, agent12108, scalar12108, tp12108, tm12108, ep12108, em12108, dsL]
  · norm_num [world12108, agent12108, scalar12108, tp12108, tm12108, ep12108, em12108, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12108, agent12108, tp12108, tm12108, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12108, agent12108, scalar12108, tp12108, tm12108, ep12108, em12108, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12108, agent12108, tp12108, tm12108, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12108, agent12108, scalar12108, tp12108, tm12108, ep12108, em12108, dsL]

theorem negative12108 :
    Eminus aL (agent12108.root+dsL) scalar12108.worldRadius world12108.frame
      agent12108.frame tm12108 ≤ -em12108 := by
  apply negative_check (lo := (16947181394524844271 / 25000000000000000000)) (hi := (13557745115619875417 / 20000000000000000000))
    (y := (-((73319961799520159169 / 100000000000000000000)))) (u := (4803695295696118107 / 10000000000000000000))
  · norm_num [world12108, agent12108, scalar12108, tp12108, tm12108, ep12108, em12108, dsL]
  · norm_num [world12108, agent12108, scalar12108, tp12108, tm12108, ep12108, em12108, dsL]
  · norm_num [world12108, agent12108, scalar12108, tp12108, tm12108, ep12108, em12108, dsL]
  · norm_num [world12108, agent12108, scalar12108, tp12108, tm12108, ep12108, em12108, dsL]
  · norm_num [world12108, agent12108, scalar12108, tp12108, tm12108, ep12108, em12108, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12108, agent12108, tp12108, tm12108, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12108, agent12108, tp12108, tm12108, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12108, agent12108, scalar12108, tp12108, tm12108, ep12108, em12108, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12108, agent12108, tp12108, tm12108, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12108, agent12108, scalar12108, tp12108, tm12108, ep12108, em12108, dsL]

theorem tails12108 :
    exp (-((12108:ℝ)*ep12108)) ≤ scalar12108.upperTail ∧
    exp (-((12108:ℝ)*em12108)) ≤ scalar12108.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12108:ℝ)) (by norm_num [ep12108]) ?_)
      (show bp12108^8 ≤ scalar12108.upperTail by norm_num [bp12108, scalar12108])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12108, bp12108, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12108:ℝ)) (by norm_num [em12108]) ?_)
      (show bm12108^8 ≤ scalar12108.lowerTail by norm_num [bm12108, scalar12108])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12108, bm12108, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12108 :
    agent12108.root+dsL+scalar12108.worldRadius < √(1/100/aL) ∧
    2*(agent12108.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12108, agent12108, scalar12108, tp12108, tm12108, ep12108, em12108, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12108, agent12108, scalar12108, tp12108, tm12108, ep12108, em12108, dsL]

noncomputable def master12108 : MasterCertificate 12108 world12108 agent12108 :=
  master scalar12108 dsL tp12108 tm12108 ep12108 em12108
    (by norm_num [dsL]) (by norm_num [tp12108]) (by norm_num [tm12108])
    (by norm_num [ep12108]) (by norm_num [em12108])
    positive12108 negative12108 tails12108.1 tails12108.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12108.1 tailGuards12108.2

theorem preserves12108 : master12108.toScalarCertificate = scalar12108 := rfl

end BstLean.Part281
