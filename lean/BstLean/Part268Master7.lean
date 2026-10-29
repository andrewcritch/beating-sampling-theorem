import BstLean.Part261Checker
import BstLean.Part268Scalar7
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12525 : ℝ := (574926727 / 2500000000)
noncomputable def tm12525 : ℝ := (-((6025619967 / 10000000000)))
noncomputable def ep12525 : ℝ := (2036897941350247 / 4000000000000000000)
noncomputable def em12525 : ℝ := (49671789645167409 / 100000000000000000000)
noncomputable def bp12525 : ℝ := (45056425357496413193 / 100000000000000000000)
noncomputable def bm12525 : ℝ := (9189470492548603199 / 20000000000000000000)

theorem positive12525 :
    Eplus aL (agent12525.root+dsL) scalar12525.worldRadius world12525.frame
      agent12525.frame tp12525 ≤ -ep12525 := by
  apply positive_check (eT := (115539337216908341383 / 100000000000000000000)) (y := (3772991757686584929 / 10000000000000000000)) (u := (145834054426581371961 / 100000000000000000000))
  · norm_num [world12525, agent12525, scalar12525, tp12525, tm12525, ep12525, em12525, dsL]
  · norm_num [world12525, agent12525, scalar12525, tp12525, tm12525, ep12525, em12525, dsL]
  · norm_num [world12525, agent12525, scalar12525, tp12525, tm12525, ep12525, em12525, dsL]
  · norm_num [world12525, agent12525, scalar12525, tp12525, tm12525, ep12525, em12525, dsL]
  · norm_num [world12525, agent12525, scalar12525, tp12525, tm12525, ep12525, em12525, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12525, agent12525, tp12525, tm12525, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12525, agent12525, scalar12525, tp12525, tm12525, ep12525, em12525, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12525, agent12525, tp12525, tm12525, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12525, agent12525, scalar12525, tp12525, tm12525, ep12525, em12525, dsL]

theorem negative12525 :
    Eminus aL (agent12525.root+dsL) scalar12525.worldRadius world12525.frame
      agent12525.frame tm12525 ≤ -em12525 := by
  apply negative_check (lo := (34245787691198280631 / 50000000000000000000)) (hi := (68491575382396561263 / 100000000000000000000))
    (y := (-((35851500484649708929 / 50000000000000000000)))) (u := (24410002717572363673 / 50000000000000000000))
  · norm_num [world12525, agent12525, scalar12525, tp12525, tm12525, ep12525, em12525, dsL]
  · norm_num [world12525, agent12525, scalar12525, tp12525, tm12525, ep12525, em12525, dsL]
  · norm_num [world12525, agent12525, scalar12525, tp12525, tm12525, ep12525, em12525, dsL]
  · norm_num [world12525, agent12525, scalar12525, tp12525, tm12525, ep12525, em12525, dsL]
  · norm_num [world12525, agent12525, scalar12525, tp12525, tm12525, ep12525, em12525, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12525, agent12525, tp12525, tm12525, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12525, agent12525, tp12525, tm12525, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12525, agent12525, scalar12525, tp12525, tm12525, ep12525, em12525, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12525, agent12525, tp12525, tm12525, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12525, agent12525, scalar12525, tp12525, tm12525, ep12525, em12525, dsL]

theorem tails12525 :
    exp (-((12525:ℝ)*ep12525)) ≤ scalar12525.upperTail ∧
    exp (-((12525:ℝ)*em12525)) ≤ scalar12525.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12525:ℝ)) (by norm_num [ep12525]) ?_)
      (show bp12525^8 ≤ scalar12525.upperTail by norm_num [bp12525, scalar12525])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12525, bp12525, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12525:ℝ)) (by norm_num [em12525]) ?_)
      (show bm12525^8 ≤ scalar12525.lowerTail by norm_num [bm12525, scalar12525])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12525, bm12525, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12525 :
    agent12525.root+dsL+scalar12525.worldRadius < √(1/100/aL) ∧
    2*(agent12525.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12525, agent12525, scalar12525, tp12525, tm12525, ep12525, em12525, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12525, agent12525, scalar12525, tp12525, tm12525, ep12525, em12525, dsL]

noncomputable def master12525 : MasterCertificate 12525 world12525 agent12525 :=
  master scalar12525 dsL tp12525 tm12525 ep12525 em12525
    (by norm_num [dsL]) (by norm_num [tp12525]) (by norm_num [tm12525])
    (by norm_num [ep12525]) (by norm_num [em12525])
    positive12525 negative12525 tails12525.1 tails12525.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12525.1 tailGuards12525.2

theorem preserves12525 : master12525.toScalarCertificate = scalar12525 := rfl

noncomputable def tp12526 : ℝ := (35934343 / 156250000)
noncomputable def tm12526 : ℝ := (-((1205163267 / 2000000000)))
noncomputable def ep12526 : ℝ := (10185053171208517 / 20000000000000000000)
noncomputable def em12526 : ℝ := (24837109607140883 / 50000000000000000000)
noncomputable def bp12526 : ℝ := (9010314020124796999 / 20000000000000000000)
noncomputable def bm12526 : ℝ := (9188550390359458367 / 20000000000000000000)

theorem positive12526 :
    Eplus aL (agent12526.root+dsL) scalar12526.worldRadius world12526.frame
      agent12526.frame tp12526 ≤ -ep12526 := by
  apply positive_check (eT := (115539619535123691221 / 100000000000000000000)) (y := (9432692582964737433 / 25000000000000000000)) (u := (145835298039064611687 / 100000000000000000000))
  · norm_num [world12526, agent12526, scalar12526, tp12526, tm12526, ep12526, em12526, dsL]
  · norm_num [world12526, agent12526, scalar12526, tp12526, tm12526, ep12526, em12526, dsL]
  · norm_num [world12526, agent12526, scalar12526, tp12526, tm12526, ep12526, em12526, dsL]
  · norm_num [world12526, agent12526, scalar12526, tp12526, tm12526, ep12526, em12526, dsL]
  · norm_num [world12526, agent12526, scalar12526, tp12526, tm12526, ep12526, em12526, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12526, agent12526, tp12526, tm12526, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12526, agent12526, scalar12526, tp12526, tm12526, ep12526, em12526, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12526, agent12526, tp12526, tm12526, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12526, agent12526, scalar12526, tp12526, tm12526, ep12526, em12526, dsL]

theorem negative12526 :
    Eminus aL (agent12526.root+dsL) scalar12526.worldRadius world12526.frame
      agent12526.frame tm12526 ≤ -em12526 := by
  apply negative_check (lo := (34245659168284293293 / 50000000000000000000)) (hi := (68491318336568586587 / 100000000000000000000))
    (y := (-((35851569947137876523 / 50000000000000000000)))) (u := (48819937612010841381 / 100000000000000000000))
  · norm_num [world12526, agent12526, scalar12526, tp12526, tm12526, ep12526, em12526, dsL]
  · norm_num [world12526, agent12526, scalar12526, tp12526, tm12526, ep12526, em12526, dsL]
  · norm_num [world12526, agent12526, scalar12526, tp12526, tm12526, ep12526, em12526, dsL]
  · norm_num [world12526, agent12526, scalar12526, tp12526, tm12526, ep12526, em12526, dsL]
  · norm_num [world12526, agent12526, scalar12526, tp12526, tm12526, ep12526, em12526, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12526, agent12526, tp12526, tm12526, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12526, agent12526, tp12526, tm12526, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12526, agent12526, scalar12526, tp12526, tm12526, ep12526, em12526, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12526, agent12526, tp12526, tm12526, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12526, agent12526, scalar12526, tp12526, tm12526, ep12526, em12526, dsL]

theorem tails12526 :
    exp (-((12526:ℝ)*ep12526)) ≤ scalar12526.upperTail ∧
    exp (-((12526:ℝ)*em12526)) ≤ scalar12526.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12526:ℝ)) (by norm_num [ep12526]) ?_)
      (show bp12526^8 ≤ scalar12526.upperTail by norm_num [bp12526, scalar12526])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12526, bp12526, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12526:ℝ)) (by norm_num [em12526]) ?_)
      (show bm12526^8 ≤ scalar12526.lowerTail by norm_num [bm12526, scalar12526])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12526, bm12526, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12526 :
    agent12526.root+dsL+scalar12526.worldRadius < √(1/100/aL) ∧
    2*(agent12526.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12526, agent12526, scalar12526, tp12526, tm12526, ep12526, em12526, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12526, agent12526, scalar12526, tp12526, tm12526, ep12526, em12526, dsL]

noncomputable def master12526 : MasterCertificate 12526 world12526 agent12526 :=
  master scalar12526 dsL tp12526 tm12526 ep12526 em12526
    (by norm_num [dsL]) (by norm_num [tp12526]) (by norm_num [tm12526])
    (by norm_num [ep12526]) (by norm_num [em12526])
    positive12526 negative12526 tails12526.1 tails12526.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12526.1 tailGuards12526.2

theorem preserves12526 : master12526.toScalarCertificate = scalar12526 := rfl

noncomputable def tp12527 : ℝ := (2299888971 / 10000000000)
noncomputable def tm12527 : ℝ := (-((376625803 / 625000000)))
noncomputable def ep12527 : ℝ := (50928081545409037 / 100000000000000000000)
noncomputable def em12527 : ℝ := (49676647299766481 / 100000000000000000000)
noncomputable def bp12527 : ℝ := (5630839525186881609 / 12500000000000000000)
noncomputable def bm12527 : ℝ := (11484538172420368959 / 25000000000000000000)

theorem positive12527 :
    Eplus aL (agent12527.root+dsL) scalar12527.worldRadius world12527.frame
      agent12527.frame tp12527 ≤ -ep12527 := by
  apply positive_check (eT := (57769950852192975683 / 50000000000000000000)) (y := (37731622998103532321 / 100000000000000000000)) (u := (145836541532725095019 / 100000000000000000000))
  · norm_num [world12527, agent12527, scalar12527, tp12527, tm12527, ep12527, em12527, dsL]
  · norm_num [world12527, agent12527, scalar12527, tp12527, tm12527, ep12527, em12527, dsL]
  · norm_num [world12527, agent12527, scalar12527, tp12527, tm12527, ep12527, em12527, dsL]
  · norm_num [world12527, agent12527, scalar12527, tp12527, tm12527, ep12527, em12527, dsL]
  · norm_num [world12527, agent12527, scalar12527, tp12527, tm12527, ep12527, em12527, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12527, agent12527, tp12527, tm12527, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12527, agent12527, scalar12527, tp12527, tm12527, ep12527, em12527, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12527, agent12527, tp12527, tm12527, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12527, agent12527, scalar12527, tp12527, tm12527, ep12527, em12527, dsL]

theorem negative12527 :
    Eminus aL (agent12527.root+dsL) scalar12527.worldRadius world12527.frame
      agent12527.frame tm12527 ≤ -em12527 := by
  apply negative_check (lo := (68491060610397311787 / 100000000000000000000)) (hi := (17122765152599327947 / 25000000000000000000))
    (y := (-((35851640432784808403 / 50000000000000000000)))) (u := (48819868789961635927 / 100000000000000000000))
  · norm_num [world12527, agent12527, scalar12527, tp12527, tm12527, ep12527, em12527, dsL]
  · norm_num [world12527, agent12527, scalar12527, tp12527, tm12527, ep12527, em12527, dsL]
  · norm_num [world12527, agent12527, scalar12527, tp12527, tm12527, ep12527, em12527, dsL]
  · norm_num [world12527, agent12527, scalar12527, tp12527, tm12527, ep12527, em12527, dsL]
  · norm_num [world12527, agent12527, scalar12527, tp12527, tm12527, ep12527, em12527, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12527, agent12527, tp12527, tm12527, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12527, agent12527, tp12527, tm12527, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12527, agent12527, scalar12527, tp12527, tm12527, ep12527, em12527, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12527, agent12527, tp12527, tm12527, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12527, agent12527, scalar12527, tp12527, tm12527, ep12527, em12527, dsL]

theorem tails12527 :
    exp (-((12527:ℝ)*ep12527)) ≤ scalar12527.upperTail ∧
    exp (-((12527:ℝ)*em12527)) ≤ scalar12527.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12527:ℝ)) (by norm_num [ep12527]) ?_)
      (show bp12527^8 ≤ scalar12527.upperTail by norm_num [bp12527, scalar12527])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12527, bp12527, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12527:ℝ)) (by norm_num [em12527]) ?_)
      (show bm12527^8 ≤ scalar12527.lowerTail by norm_num [bm12527, scalar12527])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12527, bm12527, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12527 :
    agent12527.root+dsL+scalar12527.worldRadius < √(1/100/aL) ∧
    2*(agent12527.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12527, agent12527, scalar12527, tp12527, tm12527, ep12527, em12527, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12527, agent12527, scalar12527, tp12527, tm12527, ep12527, em12527, dsL]

noncomputable def master12527 : MasterCertificate 12527 world12527 agent12527 :=
  master scalar12527 dsL tp12527 tm12527 ep12527 em12527
    (by norm_num [dsL]) (by norm_num [tp12527]) (by norm_num [tm12527])
    (by norm_num [ep12527]) (by norm_num [em12527])
    positive12527 negative12527 tails12527.1 tails12527.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12527.1 tailGuards12527.2

theorem preserves12527 : master12527.toScalarCertificate = scalar12527 := rfl

noncomputable def tp12528 : ℝ := (287497483 / 1250000000)
noncomputable def tm12528 : ℝ := (-((3013104569 / 5000000000)))
noncomputable def ep12528 : ℝ := (12732723872601121 / 25000000000000000000)
noncomputable def em12528 : ℝ := (49679073718881279 / 100000000000000000000)
noncomputable def bp12528 : ℝ := (5630232967333990453 / 12500000000000000000)
noncomputable def bm12528 : ℝ := (45933554807816924031 / 100000000000000000000)

theorem positive12528 :
    Eplus aL (agent12528.root+dsL) scalar12528.worldRadius world12528.frame
      agent12528.frame tp12528 ≤ -ep12528 := by
  apply positive_check (eT := (57770091495895441809 / 50000000000000000000)) (y := (37732474149564351917 / 100000000000000000000)) (u := (29167556565572280587 / 20000000000000000000))
  · norm_num [world12528, agent12528, scalar12528, tp12528, tm12528, ep12528, em12528, dsL]
  · norm_num [world12528, agent12528, scalar12528, tp12528, tm12528, ep12528, em12528, dsL]
  · norm_num [world12528, agent12528, scalar12528, tp12528, tm12528, ep12528, em12528, dsL]
  · norm_num [world12528, agent12528, scalar12528, tp12528, tm12528, ep12528, em12528, dsL]
  · norm_num [world12528, agent12528, scalar12528, tp12528, tm12528, ep12528, em12528, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12528, agent12528, tp12528, tm12528, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12528, agent12528, scalar12528, tp12528, tm12528, ep12528, em12528, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12528, agent12528, tp12528, tm12528, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12528, agent12528, scalar12528, tp12528, tm12528, ep12528, em12528, dsL]

theorem negative12528 :
    Eminus aL (agent12528.root+dsL) scalar12528.worldRadius world12528.frame
      agent12528.frame tm12528 ≤ -em12528 := by
  apply negative_check (lo := (68490803786918178843 / 100000000000000000000)) (hi := (17122700946729544711 / 25000000000000000000))
    (y := (-((1434068414687318147 / 2000000000000000000)))) (u := (48819800506246562601 / 100000000000000000000))
  · norm_num [world12528, agent12528, scalar12528, tp12528, tm12528, ep12528, em12528, dsL]
  · norm_num [world12528, agent12528, scalar12528, tp12528, tm12528, ep12528, em12528, dsL]
  · norm_num [world12528, agent12528, scalar12528, tp12528, tm12528, ep12528, em12528, dsL]
  · norm_num [world12528, agent12528, scalar12528, tp12528, tm12528, ep12528, em12528, dsL]
  · norm_num [world12528, agent12528, scalar12528, tp12528, tm12528, ep12528, em12528, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12528, agent12528, tp12528, tm12528, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12528, agent12528, tp12528, tm12528, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12528, agent12528, scalar12528, tp12528, tm12528, ep12528, em12528, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12528, agent12528, tp12528, tm12528, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12528, agent12528, scalar12528, tp12528, tm12528, ep12528, em12528, dsL]

theorem tails12528 :
    exp (-((12528:ℝ)*ep12528)) ≤ scalar12528.upperTail ∧
    exp (-((12528:ℝ)*em12528)) ≤ scalar12528.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12528:ℝ)) (by norm_num [ep12528]) ?_)
      (show bp12528^8 ≤ scalar12528.upperTail by norm_num [bp12528, scalar12528])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12528, bp12528, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12528:ℝ)) (by norm_num [em12528]) ?_)
      (show bm12528^8 ≤ scalar12528.lowerTail by norm_num [bm12528, scalar12528])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12528, bm12528, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12528 :
    agent12528.root+dsL+scalar12528.worldRadius < √(1/100/aL) ∧
    2*(agent12528.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12528, agent12528, scalar12528, tp12528, tm12528, ep12528, em12528, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12528, agent12528, scalar12528, tp12528, tm12528, ep12528, em12528, dsL]

noncomputable def master12528 : MasterCertificate 12528 world12528 agent12528 :=
  master scalar12528 dsL tp12528 tm12528 ep12528 em12528
    (by norm_num [dsL]) (by norm_num [tp12528]) (by norm_num [tm12528])
    (by norm_num [ep12528]) (by norm_num [em12528])
    positive12528 negative12528 tails12528.1 tails12528.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12528.1 tailGuards12528.2

theorem preserves12528 : master12528.toScalarCertificate = scalar12528 := rfl

noncomputable def tp12529 : ℝ := (1150035377 / 5000000000)
noncomputable def tm12529 : ℝ := (-((6026405347 / 10000000000)))
noncomputable def ep12529 : ℝ := (50933709062959649 / 100000000000000000000)
noncomputable def em12529 : ℝ := (49681499797115339 / 100000000000000000000)
noncomputable def bp12529 : ℝ := (45037011744425697987 / 100000000000000000000)
noncomputable def bm12529 : ℝ := (11482239338184376897 / 25000000000000000000)

theorem positive12529 :
    Eplus aL (agent12529.root+dsL) scalar12529.worldRadius world12529.frame
      agent12529.frame tp12529 ≤ -ep12529 := by
  apply positive_check (eT := (57770232144973522567 / 50000000000000000000)) (y := (37733325502932571239 / 100000000000000000000)) (u := (145839024428022839211 / 100000000000000000000))
  · norm_num [world12529, agent12529, scalar12529, tp12529, tm12529, ep12529, em12529, dsL]
  · norm_num [world12529, agent12529, scalar12529, tp12529, tm12529, ep12529, em12529, dsL]
  · norm_num [world12529, agent12529, scalar12529, tp12529, tm12529, ep12529, em12529, dsL]
  · norm_num [world12529, agent12529, scalar12529, tp12529, tm12529, ep12529, em12529, dsL]
  · norm_num [world12529, agent12529, scalar12529, tp12529, tm12529, ep12529, em12529, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12529, agent12529, tp12529, tm12529, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12529, agent12529, scalar12529, tp12529, tm12529, ep12529, em12529, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12529, agent12529, tp12529, tm12529, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12529, agent12529, scalar12529, tp12529, tm12529, ep12529, em12529, dsL]

theorem negative12529 :
    Eminus aL (agent12529.root+dsL) scalar12529.worldRadius world12529.frame
      agent12529.frame tm12529 ≤ -em12529 := by
  apply negative_check (lo := (34245273627603869311 / 50000000000000000000)) (hi := (68490547255207738623 / 100000000000000000000))
    (y := (-((14340712139220736367 / 20000000000000000000)))) (u := (9763946435450642651 / 20000000000000000000))
  · norm_num [world12529, agent12529, scalar12529, tp12529, tm12529, ep12529, em12529, dsL]
  · norm_num [world12529, agent12529, scalar12529, tp12529, tm12529, ep12529, em12529, dsL]
  · norm_num [world12529, agent12529, scalar12529, tp12529, tm12529, ep12529, em12529, dsL]
  · norm_num [world12529, agent12529, scalar12529, tp12529, tm12529, ep12529, em12529, dsL]
  · norm_num [world12529, agent12529, scalar12529, tp12529, tm12529, ep12529, em12529, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12529, agent12529, tp12529, tm12529, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12529, agent12529, tp12529, tm12529, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12529, agent12529, scalar12529, tp12529, tm12529, ep12529, em12529, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12529, agent12529, tp12529, tm12529, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12529, agent12529, scalar12529, tp12529, tm12529, ep12529, em12529, dsL]

theorem tails12529 :
    exp (-((12529:ℝ)*ep12529)) ≤ scalar12529.upperTail ∧
    exp (-((12529:ℝ)*em12529)) ≤ scalar12529.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12529:ℝ)) (by norm_num [ep12529]) ?_)
      (show bp12529^8 ≤ scalar12529.upperTail by norm_num [bp12529, scalar12529])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12529, bp12529, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12529:ℝ)) (by norm_num [em12529]) ?_)
      (show bm12529^8 ≤ scalar12529.lowerTail by norm_num [bm12529, scalar12529])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12529, bm12529, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12529 :
    agent12529.root+dsL+scalar12529.worldRadius < √(1/100/aL) ∧
    2*(agent12529.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12529, agent12529, scalar12529, tp12529, tm12529, ep12529, em12529, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12529, agent12529, scalar12529, tp12529, tm12529, ep12529, em12529, dsL]

noncomputable def master12529 : MasterCertificate 12529 world12529 agent12529 :=
  master scalar12529 dsL tp12529 tm12529 ep12529 em12529
    (by norm_num [dsL]) (by norm_num [tp12529]) (by norm_num [tm12529])
    (by norm_num [ep12529]) (by norm_num [em12529])
    positive12529 negative12529 tails12529.1 tails12529.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12529.1 tailGuards12529.2

theorem preserves12529 : master12529.toScalarCertificate = scalar12529 := rfl

noncomputable def tp12530 : ℝ := (115011877 / 500000000)
noncomputable def tm12530 : ℝ := (-((1506707697 / 2500000000)))
noncomputable def ep12530 : ℝ := (10187595809922303 / 20000000000000000000)
noncomputable def em12530 : ℝ := (6210688863555033 / 12500000000000000000)
noncomputable def bp12530 : ℝ := (11257783183836074193 / 25000000000000000000)
noncomputable def bm12530 : ℝ := (11480804998628552837 / 25000000000000000000)

theorem positive12530 :
    Eplus aL (agent12530.root+dsL) scalar12530.worldRadius world12530.frame
      agent12530.frame tp12530 ≤ -ep12530 := by
  apply positive_check (eT := (1444266204140279937 / 1250000000000000000)) (y := (471668085418069579 / 1250000000000000000)) (u := (14583920137536667029 / 10000000000000000000))
  · norm_num [world12530, agent12530, scalar12530, tp12530, tm12530, ep12530, em12530, dsL]
  · norm_num [world12530, agent12530, scalar12530, tp12530, tm12530, ep12530, em12530, dsL]
  · norm_num [world12530, agent12530, scalar12530, tp12530, tm12530, ep12530, em12530, dsL]
  · norm_num [world12530, agent12530, scalar12530, tp12530, tm12530, ep12530, em12530, dsL]
  · norm_num [world12530, agent12530, scalar12530, tp12530, tm12530, ep12530, em12530, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12530, agent12530, tp12530, tm12530, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12530, agent12530, scalar12530, tp12530, tm12530, ep12530, em12530, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12530, agent12530, tp12530, tm12530, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12530, agent12530, scalar12530, tp12530, tm12530, ep12530, em12530, dsL]

theorem negative12530 :
    Eminus aL (agent12530.root+dsL) scalar12530.worldRadius world12530.frame
      agent12530.frame tm12530 ≤ -em12530 := by
  apply negative_check (lo := (68489304683723139613 / 100000000000000000000)) (hi := (34244652341861569807 / 50000000000000000000))
    (y := (-((71701773137347452663 / 100000000000000000000)))) (u := (48820604866450408217 / 100000000000000000000))
  · norm_num [world12530, agent12530, scalar12530, tp12530, tm12530, ep12530, em12530, dsL]
  · norm_num [world12530, agent12530, scalar12530, tp12530, tm12530, ep12530, em12530, dsL]
  · norm_num [world12530, agent12530, scalar12530, tp12530, tm12530, ep12530, em12530, dsL]
  · norm_num [world12530, agent12530, scalar12530, tp12530, tm12530, ep12530, em12530, dsL]
  · norm_num [world12530, agent12530, scalar12530, tp12530, tm12530, ep12530, em12530, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12530, agent12530, tp12530, tm12530, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12530, agent12530, tp12530, tm12530, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12530, agent12530, scalar12530, tp12530, tm12530, ep12530, em12530, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12530, agent12530, tp12530, tm12530, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12530, agent12530, scalar12530, tp12530, tm12530, ep12530, em12530, dsL]

theorem tails12530 :
    exp (-((12530:ℝ)*ep12530)) ≤ scalar12530.upperTail ∧
    exp (-((12530:ℝ)*em12530)) ≤ scalar12530.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12530:ℝ)) (by norm_num [ep12530]) ?_)
      (show bp12530^8 ≤ scalar12530.upperTail by norm_num [bp12530, scalar12530])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12530, bp12530, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12530:ℝ)) (by norm_num [em12530]) ?_)
      (show bm12530^8 ≤ scalar12530.lowerTail by norm_num [bm12530, scalar12530])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12530, bm12530, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12530 :
    agent12530.root+dsL+scalar12530.worldRadius < √(1/100/aL) ∧
    2*(agent12530.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12530, agent12530, scalar12530, tp12530, tm12530, ep12530, em12530, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12530, agent12530, scalar12530, tp12530, tm12530, ep12530, em12530, dsL]

noncomputable def master12530 : MasterCertificate 12530 world12530 agent12530 :=
  master scalar12530 dsL tp12530 tm12530 ep12530 em12530
    (by norm_num [dsL]) (by norm_num [tp12530]) (by norm_num [tm12530])
    (by norm_num [ep12530]) (by norm_num [em12530])
    positive12530 negative12530 tails12530.1 tails12530.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12530.1 tailGuards12530.2

theorem preserves12530 : master12530.toScalarCertificate = scalar12530 := rfl

noncomputable def tp12531 : ℝ := (2300328351 / 10000000000)
noncomputable def tm12531 : ℝ := (-((6027026843 / 10000000000)))
noncomputable def ep12531 : ℝ := (10188157806388311 / 20000000000000000000)
noncomputable def em12531 : ℝ := (49687933662013467 / 100000000000000000000)
noncomputable def bp12531 : ℝ := (22513141856891381143 / 50000000000000000000)
noncomputable def bm12531 : ℝ := (22959312658568947669 / 50000000000000000000)

theorem positive12531 :
    Eplus aL (agent12531.root+dsL) scalar12531.worldRadius world12531.frame
      agent12531.frame tp12531 ≤ -ep12531 := by
  apply positive_check (eT := (23108315421995492103 / 20000000000000000000)) (y := (37734297657287787379 / 100000000000000000000)) (u := (9115027638458871899 / 6250000000000000000))
  · norm_num [world12531, agent12531, scalar12531, tp12531, tm12531, ep12531, em12531, dsL]
  · norm_num [world12531, agent12531, scalar12531, tp12531, tm12531, ep12531, em12531, dsL]
  · norm_num [world12531, agent12531, scalar12531, tp12531, tm12531, ep12531, em12531, dsL]
  · norm_num [world12531, agent12531, scalar12531, tp12531, tm12531, ep12531, em12531, dsL]
  · norm_num [world12531, agent12531, scalar12531, tp12531, tm12531, ep12531, em12531, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12531, agent12531, tp12531, tm12531, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12531, agent12531, scalar12531, tp12531, tm12531, ep12531, em12531, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12531, agent12531, tp12531, tm12531, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12531, agent12531, scalar12531, tp12531, tm12531, ep12531, em12531, dsL]

theorem negative12531 :
    Eminus aL (agent12531.root+dsL) scalar12531.worldRadius world12531.frame
      agent12531.frame tm12531 ≤ -em12531 := by
  apply negative_check (lo := (34244524363614601503 / 50000000000000000000)) (hi := (68489048727229203007 / 100000000000000000000))
    (y := (-((7170191275579479151 / 10000000000000000000)))) (u := (9764107340785499197 / 20000000000000000000))
  · norm_num [world12531, agent12531, scalar12531, tp12531, tm12531, ep12531, em12531, dsL]
  · norm_num [world12531, agent12531, scalar12531, tp12531, tm12531, ep12531, em12531, dsL]
  · norm_num [world12531, agent12531, scalar12531, tp12531, tm12531, ep12531, em12531, dsL]
  · norm_num [world12531, agent12531, scalar12531, tp12531, tm12531, ep12531, em12531, dsL]
  · norm_num [world12531, agent12531, scalar12531, tp12531, tm12531, ep12531, em12531, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12531, agent12531, tp12531, tm12531, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12531, agent12531, tp12531, tm12531, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12531, agent12531, scalar12531, tp12531, tm12531, ep12531, em12531, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12531, agent12531, tp12531, tm12531, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12531, agent12531, scalar12531, tp12531, tm12531, ep12531, em12531, dsL]

theorem tails12531 :
    exp (-((12531:ℝ)*ep12531)) ≤ scalar12531.upperTail ∧
    exp (-((12531:ℝ)*em12531)) ≤ scalar12531.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12531:ℝ)) (by norm_num [ep12531]) ?_)
      (show bp12531^8 ≤ scalar12531.upperTail by norm_num [bp12531, scalar12531])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12531, bp12531, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12531:ℝ)) (by norm_num [em12531]) ?_)
      (show bm12531^8 ≤ scalar12531.lowerTail by norm_num [bm12531, scalar12531])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12531, bm12531, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12531 :
    agent12531.root+dsL+scalar12531.worldRadius < √(1/100/aL) ∧
    2*(agent12531.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12531, agent12531, scalar12531, tp12531, tm12531, ep12531, em12531, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12531, agent12531, scalar12531, tp12531, tm12531, ep12531, em12531, dsL]

noncomputable def master12531 : MasterCertificate 12531 world12531 agent12531 :=
  master scalar12531 dsL tp12531 tm12531 ep12531 em12531
    (by norm_num [dsL]) (by norm_num [tp12531]) (by norm_num [tm12531])
    (by norm_num [ep12531]) (by norm_num [em12531])
    positive12531 negative12531 tails12531.1 tails12531.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12531.1 tailGuards12531.2

theorem preserves12531 : master12531.toScalarCertificate = scalar12531 := rfl

noncomputable def tp12532 : ℝ := (2300419113 / 10000000000)
noncomputable def tm12532 : ℝ := (-((188350709 / 312500000)))
noncomputable def ep12532 : ℝ := (25471799016444407 / 50000000000000000000)
noncomputable def em12532 : ℝ := (49690355494630073 / 100000000000000000000)
noncomputable def bp12532 : ℝ := (1800857423609140643 / 4000000000000000000)
noncomputable def bm12532 : ℝ := (45914031483760879173 / 100000000000000000000)

theorem positive12532 :
    Eplus aL (agent12532.root+dsL) scalar12532.worldRadius world12532.frame
      agent12532.frame tp12532 ≤ -ep12532 := by
  apply positive_check (eT := (115541857565685164957 / 100000000000000000000)) (y := (9433787018071560057 / 25000000000000000000)) (u := (29168336493922001259 / 20000000000000000000))
  · norm_num [world12532, agent12532, scalar12532, tp12532, tm12532, ep12532, em12532, dsL]
  · norm_num [world12532, agent12532, scalar12532, tp12532, tm12532, ep12532, em12532, dsL]
  · norm_num [world12532, agent12532, scalar12532, tp12532, tm12532, ep12532, em12532, dsL]
  · norm_num [world12532, agent12532, scalar12532, tp12532, tm12532, ep12532, em12532, dsL]
  · norm_num [world12532, agent12532, scalar12532, tp12532, tm12532, ep12532, em12532, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12532, agent12532, tp12532, tm12532, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12532, agent12532, scalar12532, tp12532, tm12532, ep12532, em12532, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12532, agent12532, tp12532, tm12532, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12532, agent12532, scalar12532, tp12532, tm12532, ep12532, em12532, dsL]

theorem negative12532 :
    Eminus aL (agent12532.root+dsL) scalar12532.worldRadius world12532.frame
      agent12532.frame tm12532 ≤ -em12532 := by
  apply negative_check (lo := (8561099202167513577 / 12500000000000000000)) (hi := (68488793617340108617 / 100000000000000000000))
    (y := (-((71702051363167916023 / 100000000000000000000)))) (u := (24410234517555461189 / 50000000000000000000))
  · norm_num [world12532, agent12532, scalar12532, tp12532, tm12532, ep12532, em12532, dsL]
  · norm_num [world12532, agent12532, scalar12532, tp12532, tm12532, ep12532, em12532, dsL]
  · norm_num [world12532, agent12532, scalar12532, tp12532, tm12532, ep12532, em12532, dsL]
  · norm_num [world12532, agent12532, scalar12532, tp12532, tm12532, ep12532, em12532, dsL]
  · norm_num [world12532, agent12532, scalar12532, tp12532, tm12532, ep12532, em12532, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12532, agent12532, tp12532, tm12532, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12532, agent12532, tp12532, tm12532, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12532, agent12532, scalar12532, tp12532, tm12532, ep12532, em12532, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12532, agent12532, tp12532, tm12532, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12532, agent12532, scalar12532, tp12532, tm12532, ep12532, em12532, dsL]

theorem tails12532 :
    exp (-((12532:ℝ)*ep12532)) ≤ scalar12532.upperTail ∧
    exp (-((12532:ℝ)*em12532)) ≤ scalar12532.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12532:ℝ)) (by norm_num [ep12532]) ?_)
      (show bp12532^8 ≤ scalar12532.upperTail by norm_num [bp12532, scalar12532])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12532, bp12532, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12532:ℝ)) (by norm_num [em12532]) ?_)
      (show bm12532^8 ≤ scalar12532.lowerTail by norm_num [bm12532, scalar12532])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12532, bm12532, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12532 :
    agent12532.root+dsL+scalar12532.worldRadius < √(1/100/aL) ∧
    2*(agent12532.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12532, agent12532, scalar12532, tp12532, tm12532, ep12532, em12532, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12532, agent12532, scalar12532, tp12532, tm12532, ep12532, em12532, dsL]

noncomputable def master12532 : MasterCertificate 12532 world12532 agent12532 :=
  master scalar12532 dsL tp12532 tm12532 ep12532 em12532
    (by norm_num [dsL]) (by norm_num [tp12532]) (by norm_num [tm12532])
    (by norm_num [ep12532]) (by norm_num [em12532])
    positive12532 negative12532 tails12532.1 tails12532.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12532.1 tailGuards12532.2

theorem preserves12532 : master12532.toScalarCertificate = scalar12532 := rfl

noncomputable def tp12533 : ℝ := (2300509883 / 10000000000)
noncomputable def tm12533 : ℝ := (-((94178413 / 156250000)))
noncomputable def ep12533 : ℝ := (25473202628434271 / 50000000000000000000)
noncomputable def em12533 : ℝ := (4969277568748573 / 10000000000000000000)
noncomputable def bp12533 : ℝ := (45016588925748681963 / 100000000000000000000)
noncomputable def bm12533 : ℝ := (1836377560454605393 / 4000000000000000000)

theorem positive12533 :
    Eplus aL (agent12533.root+dsL) scalar12533.worldRadius world12533.frame
      agent12533.frame tp12533 ≤ -ep12533 := by
  apply positive_check (eT := (57771069055961442349 / 50000000000000000000)) (y := (37735999028363276089 / 100000000000000000000)) (u := (72921461761775118629 / 50000000000000000000))
  · norm_num [world12533, agent12533, scalar12533, tp12533, tm12533, ep12533, em12533, dsL]
  · norm_num [world12533, agent12533, scalar12533, tp12533, tm12533, ep12533, em12533, dsL]
  · norm_num [world12533, agent12533, scalar12533, tp12533, tm12533, ep12533, em12533, dsL]
  · norm_num [world12533, agent12533, scalar12533, tp12533, tm12533, ep12533, em12533, dsL]
  · norm_num [world12533, agent12533, scalar12533, tp12533, tm12533, ep12533, em12533, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12533, agent12533, tp12533, tm12533, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12533, agent12533, scalar12533, tp12533, tm12533, ep12533, em12533, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12533, agent12533, tp12533, tm12533, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12533, agent12533, scalar12533, tp12533, tm12533, ep12533, em12533, dsL]

theorem negative12533 :
    Eminus aL (agent12533.root+dsL) scalar12533.worldRadius world12533.frame
      agent12533.frame tm12533 ≤ -em12533 := by
  apply negative_check (lo := (34244269442610823087 / 50000000000000000000)) (hi := (2739541555408865847 / 4000000000000000000))
    (y := (-((35851094740648863813 / 50000000000000000000)))) (u := (1220510040130967307 / 2500000000000000000))
  · norm_num [world12533, agent12533, scalar12533, tp12533, tm12533, ep12533, em12533, dsL]
  · norm_num [world12533, agent12533, scalar12533, tp12533, tm12533, ep12533, em12533, dsL]
  · norm_num [world12533, agent12533, scalar12533, tp12533, tm12533, ep12533, em12533, dsL]
  · norm_num [world12533, agent12533, scalar12533, tp12533, tm12533, ep12533, em12533, dsL]
  · norm_num [world12533, agent12533, scalar12533, tp12533, tm12533, ep12533, em12533, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12533, agent12533, tp12533, tm12533, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12533, agent12533, tp12533, tm12533, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12533, agent12533, scalar12533, tp12533, tm12533, ep12533, em12533, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12533, agent12533, tp12533, tm12533, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12533, agent12533, scalar12533, tp12533, tm12533, ep12533, em12533, dsL]

theorem tails12533 :
    exp (-((12533:ℝ)*ep12533)) ≤ scalar12533.upperTail ∧
    exp (-((12533:ℝ)*em12533)) ≤ scalar12533.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12533:ℝ)) (by norm_num [ep12533]) ?_)
      (show bp12533^8 ≤ scalar12533.upperTail by norm_num [bp12533, scalar12533])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12533, bp12533, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12533:ℝ)) (by norm_num [em12533]) ?_)
      (show bm12533^8 ≤ scalar12533.lowerTail by norm_num [bm12533, scalar12533])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12533, bm12533, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12533 :
    agent12533.root+dsL+scalar12533.worldRadius < √(1/100/aL) ∧
    2*(agent12533.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12533, agent12533, scalar12533, tp12533, tm12533, ep12533, em12533, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12533, agent12533, scalar12533, tp12533, tm12533, ep12533, em12533, dsL]

noncomputable def master12533 : MasterCertificate 12533 world12533 agent12533 :=
  master scalar12533 dsL tp12533 tm12533 ep12533 em12533
    (by norm_num [dsL]) (by norm_num [tp12533]) (by norm_num [tm12533])
    (by norm_num [ep12533]) (by norm_num [em12533])
    positive12533 negative12533 tails12533.1 tails12533.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12533.1 tailGuards12533.2

theorem preserves12533 : master12533.toScalarCertificate = scalar12533 := rfl

noncomputable def tp12534 : ℝ := (2300600491 / 10000000000)
noncomputable def tm12534 : ℝ := (-((3013807111 / 5000000000)))
noncomputable def ep12534 : ℝ := (50949211031207453 / 100000000000000000000)
noncomputable def em12534 : ℝ := (12423798631594829 / 25000000000000000000)
noncomputable def bp12534 : ℝ := (5626467936180816259 / 12500000000000000000)
noncomputable def bm12534 : ℝ := (45904847694365862757 / 100000000000000000000)

theorem positive12534 :
    Eplus aL (agent12534.root+dsL) scalar12534.worldRadius world12534.frame
      agent12534.frame tp12534 ≤ -ep12534 := by
  apply positive_check (eT := (115542417515277295381 / 100000000000000000000)) (y := (9434211908328913347 / 25000000000000000000)) (u := (29168832231814652137 / 20000000000000000000))
  · norm_num [world12534, agent12534, scalar12534, tp12534, tm12534, ep12534, em12534, dsL]
  · norm_num [world12534, agent12534, scalar12534, tp12534, tm12534, ep12534, em12534, dsL]
  · norm_num [world12534, agent12534, scalar12534, tp12534, tm12534, ep12534, em12534, dsL]
  · norm_num [world12534, agent12534, scalar12534, tp12534, tm12534, ep12534, em12534, dsL]
  · norm_num [world12534, agent12534, scalar12534, tp12534, tm12534, ep12534, em12534, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12534, agent12534, tp12534, tm12534, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12534, agent12534, scalar12534, tp12534, tm12534, ep12534, em12534, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12534, agent12534, tp12534, tm12534, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12534, agent12534, scalar12534, tp12534, tm12534, ep12534, em12534, dsL]

theorem negative12534 :
    Eminus aL (agent12534.root+dsL) scalar12534.worldRadius world12534.frame
      agent12534.frame tm12534 ≤ -em12534 := by
  apply negative_check (lo := (13697656779715520087 / 20000000000000000000)) (hi := (17122070974644400109 / 25000000000000000000))
    (y := (-((71702328964638785853 / 100000000000000000000)))) (u := (48820333508958906743 / 100000000000000000000))
  · norm_num [world12534, agent12534, scalar12534, tp12534, tm12534, ep12534, em12534, dsL]
  · norm_num [world12534, agent12534, scalar12534, tp12534, tm12534, ep12534, em12534, dsL]
  · norm_num [world12534, agent12534, scalar12534, tp12534, tm12534, ep12534, em12534, dsL]
  · norm_num [world12534, agent12534, scalar12534, tp12534, tm12534, ep12534, em12534, dsL]
  · norm_num [world12534, agent12534, scalar12534, tp12534, tm12534, ep12534, em12534, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12534, agent12534, tp12534, tm12534, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12534, agent12534, tp12534, tm12534, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12534, agent12534, scalar12534, tp12534, tm12534, ep12534, em12534, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12534, agent12534, tp12534, tm12534, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12534, agent12534, scalar12534, tp12534, tm12534, ep12534, em12534, dsL]

theorem tails12534 :
    exp (-((12534:ℝ)*ep12534)) ≤ scalar12534.upperTail ∧
    exp (-((12534:ℝ)*em12534)) ≤ scalar12534.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12534:ℝ)) (by norm_num [ep12534]) ?_)
      (show bp12534^8 ≤ scalar12534.upperTail by norm_num [bp12534, scalar12534])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12534, bp12534, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12534:ℝ)) (by norm_num [em12534]) ?_)
      (show bm12534^8 ≤ scalar12534.lowerTail by norm_num [bm12534, scalar12534])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12534, bm12534, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12534 :
    agent12534.root+dsL+scalar12534.worldRadius < √(1/100/aL) ∧
    2*(agent12534.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12534, agent12534, scalar12534, tp12534, tm12534, ep12534, em12534, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12534, agent12534, scalar12534, tp12534, tm12534, ep12534, em12534, dsL]

noncomputable def master12534 : MasterCertificate 12534 world12534 agent12534 :=
  master scalar12534 dsL tp12534 tm12534 ep12534 em12534
    (by norm_num [dsL]) (by norm_num [tp12534]) (by norm_num [tm12534])
    (by norm_num [ep12534]) (by norm_num [em12534])
    positive12534 negative12534 tails12534.1 tails12534.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12534.1 tailGuards12534.2

theorem preserves12534 : master12534.toScalarCertificate = scalar12534 := rfl

noncomputable def tp12535 : ℝ := (2300691141 / 10000000000)
noncomputable def tm12535 : ℝ := (-((1205561941 / 2000000000)))
noncomputable def ep12535 : ℝ := (6369001978629291 / 12500000000000000000)
noncomputable def em12535 : ℝ := (49697612448639529 / 100000000000000000000)
noncomputable def bp12535 : ℝ := (45006898947631153751 / 100000000000000000000)
noncomputable def bm12535 : ℝ := (22950128609107344649 / 50000000000000000000)

theorem positive12535 :
    Eplus aL (agent12535.root+dsL) scalar12535.worldRadius world12535.frame
      agent12535.frame tp12535 ≤ -ep12535 := by
  apply positive_check (eT := (57771348627938414577 / 50000000000000000000)) (y := (37737697431941637263 / 100000000000000000000)) (u := (145845400546017007349 / 100000000000000000000))
  · norm_num [world12535, agent12535, scalar12535, tp12535, tm12535, ep12535, em12535, dsL]
  · norm_num [world12535, agent12535, scalar12535, tp12535, tm12535, ep12535, em12535, dsL]
  · norm_num [world12535, agent12535, scalar12535, tp12535, tm12535, ep12535, em12535, dsL]
  · norm_num [world12535, agent12535, scalar12535, tp12535, tm12535, ep12535, em12535, dsL]
  · norm_num [world12535, agent12535, scalar12535, tp12535, tm12535, ep12535, em12535, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12535, agent12535, tp12535, tm12535, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12535, agent12535, scalar12535, tp12535, tm12535, ep12535, em12535, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12535, agent12535, tp12535, tm12535, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12535, agent12535, scalar12535, tp12535, tm12535, ep12535, em12535, dsL]

theorem negative12535 :
    Eminus aL (agent12535.root+dsL) scalar12535.worldRadius world12535.frame
      agent12535.frame tm12535 ≤ -em12535 := by
  apply negative_check (lo := (34244015087813070401 / 50000000000000000000)) (hi := (68488030175626140803 / 100000000000000000000))
    (y := (-((8962808310825983763 / 12500000000000000000)))) (u := (48820266370321116923 / 100000000000000000000))
  · norm_num [world12535, agent12535, scalar12535, tp12535, tm12535, ep12535, em12535, dsL]
  · norm_num [world12535, agent12535, scalar12535, tp12535, tm12535, ep12535, em12535, dsL]
  · norm_num [world12535, agent12535, scalar12535, tp12535, tm12535, ep12535, em12535, dsL]
  · norm_num [world12535, agent12535, scalar12535, tp12535, tm12535, ep12535, em12535, dsL]
  · norm_num [world12535, agent12535, scalar12535, tp12535, tm12535, ep12535, em12535, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12535, agent12535, tp12535, tm12535, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12535, agent12535, tp12535, tm12535, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12535, agent12535, scalar12535, tp12535, tm12535, ep12535, em12535, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12535, agent12535, tp12535, tm12535, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12535, agent12535, scalar12535, tp12535, tm12535, ep12535, em12535, dsL]

theorem tails12535 :
    exp (-((12535:ℝ)*ep12535)) ≤ scalar12535.upperTail ∧
    exp (-((12535:ℝ)*em12535)) ≤ scalar12535.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12535:ℝ)) (by norm_num [ep12535]) ?_)
      (show bp12535^8 ≤ scalar12535.upperTail by norm_num [bp12535, scalar12535])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12535, bp12535, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12535:ℝ)) (by norm_num [em12535]) ?_)
      (show bm12535^8 ≤ scalar12535.lowerTail by norm_num [bm12535, scalar12535])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12535, bm12535, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12535 :
    agent12535.root+dsL+scalar12535.worldRadius < √(1/100/aL) ∧
    2*(agent12535.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12535, agent12535, scalar12535, tp12535, tm12535, ep12535, em12535, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12535, agent12535, scalar12535, tp12535, tm12535, ep12535, em12535, dsL]

noncomputable def master12535 : MasterCertificate 12535 world12535 agent12535 :=
  master scalar12535 dsL tp12535 tm12535 ep12535 em12535
    (by norm_num [dsL]) (by norm_num [tp12535]) (by norm_num [tm12535])
    (by norm_num [ep12535]) (by norm_num [em12535])
    positive12535 negative12535 tails12535.1 tails12535.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12535.1 tailGuards12535.2

theorem preserves12535 : master12535.toScalarCertificate = scalar12535 := rfl

noncomputable def tp12536 : ℝ := (575195433 / 2500000000)
noncomputable def tm12536 : ℝ := (-((6028005303 / 10000000000)))
noncomputable def ep12536 : ℝ := (10190963769996883 / 20000000000000000000)
noncomputable def em12536 : ℝ := (49700028731364849 / 100000000000000000000)
noncomputable def bp12536 : ℝ := (11250513966173444487 / 25000000000000000000)
noncomputable def bm12536 : ℝ := (45895668102808963799 / 100000000000000000000)

theorem positive12536 :
    Eplus aL (agent12536.root+dsL) scalar12536.worldRadius world12536.frame
      agent12536.frame tp12536 ≤ -ep12536 := by
  apply positive_check (eT := (115542976600929358591 / 100000000000000000000)) (y := (18869273295381577739 / 50000000000000000000)) (u := (72923319505179889797 / 50000000000000000000))
  · norm_num [world12536, agent12536, scalar12536, tp12536, tm12536, ep12536, em12536, dsL]
  · norm_num [world12536, agent12536, scalar12536, tp12536, tm12536, ep12536, em12536, dsL]
  · norm_num [world12536, agent12536, scalar12536, tp12536, tm12536, ep12536, em12536, dsL]
  · norm_num [world12536, agent12536, scalar12536, tp12536, tm12536, ep12536, em12536, dsL]
  · norm_num [world12536, agent12536, scalar12536, tp12536, tm12536, ep12536, em12536, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12536, agent12536, tp12536, tm12536, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12536, agent12536, scalar12536, tp12536, tm12536, ep12536, em12536, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12536, agent12536, tp12536, tm12536, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12536, agent12536, scalar12536, tp12536, tm12536, ep12536, em12536, dsL]

theorem negative12536 :
    Eminus aL (agent12536.root+dsL) scalar12536.worldRadius world12536.frame
      agent12536.frame tm12536 ≤ -em12536 := by
  apply negative_check (lo := (34243887950714337941 / 50000000000000000000)) (hi := (68487775901428675883 / 100000000000000000000))
    (y := (-((71702605631863657093 / 100000000000000000000)))) (u := (48820198439283861469 / 100000000000000000000))
  · norm_num [world12536, agent12536, scalar12536, tp12536, tm12536, ep12536, em12536, dsL]
  · norm_num [world12536, agent12536, scalar12536, tp12536, tm12536, ep12536, em12536, dsL]
  · norm_num [world12536, agent12536, scalar12536, tp12536, tm12536, ep12536, em12536, dsL]
  · norm_num [world12536, agent12536, scalar12536, tp12536, tm12536, ep12536, em12536, dsL]
  · norm_num [world12536, agent12536, scalar12536, tp12536, tm12536, ep12536, em12536, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12536, agent12536, tp12536, tm12536, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12536, agent12536, tp12536, tm12536, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12536, agent12536, scalar12536, tp12536, tm12536, ep12536, em12536, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12536, agent12536, tp12536, tm12536, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12536, agent12536, scalar12536, tp12536, tm12536, ep12536, em12536, dsL]

theorem tails12536 :
    exp (-((12536:ℝ)*ep12536)) ≤ scalar12536.upperTail ∧
    exp (-((12536:ℝ)*em12536)) ≤ scalar12536.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12536:ℝ)) (by norm_num [ep12536]) ?_)
      (show bp12536^8 ≤ scalar12536.upperTail by norm_num [bp12536, scalar12536])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12536, bp12536, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12536:ℝ)) (by norm_num [em12536]) ?_)
      (show bm12536^8 ≤ scalar12536.lowerTail by norm_num [bm12536, scalar12536])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12536, bm12536, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12536 :
    agent12536.root+dsL+scalar12536.worldRadius < √(1/100/aL) ∧
    2*(agent12536.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12536, agent12536, scalar12536, tp12536, tm12536, ep12536, em12536, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12536, agent12536, scalar12536, tp12536, tm12536, ep12536, em12536, dsL]

noncomputable def master12536 : MasterCertificate 12536 world12536 agent12536 :=
  master scalar12536 dsL tp12536 tm12536 ep12536 em12536
    (by norm_num [dsL]) (by norm_num [tp12536]) (by norm_num [tm12536])
    (by norm_num [ep12536]) (by norm_num [em12536])
    positive12536 negative12536 tails12536.1 tails12536.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12536.1 tailGuards12536.2

theorem preserves12536 : master12536.toScalarCertificate = scalar12536 := rfl

noncomputable def tp12537 : ℝ := (575218073 / 2500000000)
noncomputable def tm12537 : ℝ := (-((6028200649 / 10000000000)))
noncomputable def ep12537 : ℝ := (25478810213092051 / 50000000000000000000)
noncomputable def em12537 : ℝ := (2485122183223189 / 5000000000000000000)
noncomputable def bp12537 : ℝ := (44997214006372373063 / 100000000000000000000)
noncomputable def bm12537 : ℝ := (45891080139620805577 / 100000000000000000000)

theorem positive12537 :
    Eplus aL (agent12537.root+dsL) scalar12537.worldRadius world12537.frame
      agent12537.frame tp12537 ≤ -ep12537 := by
  apply positive_check (eT := (115543255753558337551 / 100000000000000000000)) (y := (37739395705599947017 / 100000000000000000000)) (u := (145847877421068335449 / 100000000000000000000))
  · norm_num [world12537, agent12537, scalar12537, tp12537, tm12537, ep12537, em12537, dsL]
  · norm_num [world12537, agent12537, scalar12537, tp12537, tm12537, ep12537, em12537, dsL]
  · norm_num [world12537, agent12537, scalar12537, tp12537, tm12537, ep12537, em12537, dsL]
  · norm_num [world12537, agent12537, scalar12537, tp12537, tm12537, ep12537, em12537, dsL]
  · norm_num [world12537, agent12537, scalar12537, tp12537, tm12537, ep12537, em12537, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12537, agent12537, tp12537, tm12537, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12537, agent12537, scalar12537, tp12537, tm12537, ep12537, em12537, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12537, agent12537, tp12537, tm12537, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12537, agent12537, scalar12537, tp12537, tm12537, ep12537, em12537, dsL]

theorem negative12537 :
    Eminus aL (agent12537.root+dsL) scalar12537.worldRadius world12537.frame
      agent12537.frame tm12537 ≤ -em12537 := by
  apply negative_check (lo := (68487522654352755069 / 100000000000000000000)) (hi := (6848752265435275507 / 10000000000000000000))
    (y := (-((71702743224967338031 / 100000000000000000000)))) (u := (12205032816525954627 / 25000000000000000000))
  · norm_num [world12537, agent12537, scalar12537, tp12537, tm12537, ep12537, em12537, dsL]
  · norm_num [world12537, agent12537, scalar12537, tp12537, tm12537, ep12537, em12537, dsL]
  · norm_num [world12537, agent12537, scalar12537, tp12537, tm12537, ep12537, em12537, dsL]
  · norm_num [world12537, agent12537, scalar12537, tp12537, tm12537, ep12537, em12537, dsL]
  · norm_num [world12537, agent12537, scalar12537, tp12537, tm12537, ep12537, em12537, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12537, agent12537, tp12537, tm12537, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12537, agent12537, tp12537, tm12537, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12537, agent12537, scalar12537, tp12537, tm12537, ep12537, em12537, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12537, agent12537, tp12537, tm12537, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12537, agent12537, scalar12537, tp12537, tm12537, ep12537, em12537, dsL]

theorem tails12537 :
    exp (-((12537:ℝ)*ep12537)) ≤ scalar12537.upperTail ∧
    exp (-((12537:ℝ)*em12537)) ≤ scalar12537.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12537:ℝ)) (by norm_num [ep12537]) ?_)
      (show bp12537^8 ≤ scalar12537.upperTail by norm_num [bp12537, scalar12537])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12537, bp12537, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12537:ℝ)) (by norm_num [em12537]) ?_)
      (show bm12537^8 ≤ scalar12537.lowerTail by norm_num [bm12537, scalar12537])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12537, bm12537, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12537 :
    agent12537.root+dsL+scalar12537.worldRadius < √(1/100/aL) ∧
    2*(agent12537.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12537, agent12537, scalar12537, tp12537, tm12537, ep12537, em12537, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12537, agent12537, scalar12537, tp12537, tm12537, ep12537, em12537, dsL]

noncomputable def master12537 : MasterCertificate 12537 world12537 agent12537 :=
  master scalar12537 dsL tp12537 tm12537 ep12537 em12537
    (by norm_num [dsL]) (by norm_num [tp12537]) (by norm_num [tm12537])
    (by norm_num [ep12537]) (by norm_num [em12537])
    positive12537 negative12537 tails12537.1 tails12537.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12537.1 tailGuards12537.2

theorem preserves12537 : master12537.toScalarCertificate = scalar12537 := rfl

noncomputable def tp12538 : ℝ := (2300962777 / 10000000000)
noncomputable def tm12538 : ℝ := (-((6028395877 / 10000000000)))
noncomputable def ep12538 : ℝ := (25480210278799169 / 50000000000000000000)
noncomputable def em12538 : ℝ := (49704857247956393 / 100000000000000000000)
noncomputable def bp12538 : ℝ := (22496186686326137201 / 50000000000000000000)
noncomputable def bm12538 : ℝ := (45886493328614197153 / 100000000000000000000)

theorem positive12538 :
    Eplus aL (agent12538.root+dsL) scalar12538.worldRadius world12538.frame
      agent12538.frame tp12538 ≤ -ep12538 := by
  apply positive_check (eT := (115543534394619600363 / 100000000000000000000)) (y := (18870122000603810409 / 50000000000000000000)) (u := (29169822929490808993 / 20000000000000000000))
  · norm_num [world12538, agent12538, scalar12538, tp12538, tm12538, ep12538, em12538, dsL]
  · norm_num [world12538, agent12538, scalar12538, tp12538, tm12538, ep12538, em12538, dsL]
  · norm_num [world12538, agent12538, scalar12538, tp12538, tm12538, ep12538, em12538, dsL]
  · norm_num [world12538, agent12538, scalar12538, tp12538, tm12538, ep12538, em12538, dsL]
  · norm_num [world12538, agent12538, scalar12538, tp12538, tm12538, ep12538, em12538, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12538, agent12538, tp12538, tm12538, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12538, agent12538, scalar12538, tp12538, tm12538, ep12538, em12538, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12538, agent12538, tp12538, tm12538, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12538, agent12538, scalar12538, tp12538, tm12538, ep12538, em12538, dsL]

theorem negative12538 :
    Eminus aL (agent12538.root+dsL) scalar12538.worldRadius world12538.frame
      agent12538.frame tm12538 ≤ -em12538 := by
  apply negative_check (lo := (34243634928990127503 / 50000000000000000000)) (hi := (68487269857980255007 / 100000000000000000000))
    (y := (-((71702880576816042811 / 100000000000000000000)))) (u := (12205016052699258819 / 25000000000000000000))
  · norm_num [world12538, agent12538, scalar12538, tp12538, tm12538, ep12538, em12538, dsL]
  · norm_num [world12538, agent12538, scalar12538, tp12538, tm12538, ep12538, em12538, dsL]
  · norm_num [world12538, agent12538, scalar12538, tp12538, tm12538, ep12538, em12538, dsL]
  · norm_num [world12538, agent12538, scalar12538, tp12538, tm12538, ep12538, em12538, dsL]
  · norm_num [world12538, agent12538, scalar12538, tp12538, tm12538, ep12538, em12538, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12538, agent12538, tp12538, tm12538, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12538, agent12538, tp12538, tm12538, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12538, agent12538, scalar12538, tp12538, tm12538, ep12538, em12538, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12538, agent12538, tp12538, tm12538, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12538, agent12538, scalar12538, tp12538, tm12538, ep12538, em12538, dsL]

theorem tails12538 :
    exp (-((12538:ℝ)*ep12538)) ≤ scalar12538.upperTail ∧
    exp (-((12538:ℝ)*em12538)) ≤ scalar12538.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12538:ℝ)) (by norm_num [ep12538]) ?_)
      (show bp12538^8 ≤ scalar12538.upperTail by norm_num [bp12538, scalar12538])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12538, bp12538, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12538:ℝ)) (by norm_num [em12538]) ?_)
      (show bm12538^8 ≤ scalar12538.lowerTail by norm_num [bm12538, scalar12538])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12538, bm12538, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12538 :
    agent12538.root+dsL+scalar12538.worldRadius < √(1/100/aL) ∧
    2*(agent12538.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12538, agent12538, scalar12538, tp12538, tm12538, ep12538, em12538, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12538, agent12538, scalar12538, tp12538, tm12538, ep12538, em12538, dsL]

noncomputable def master12538 : MasterCertificate 12538 world12538 agent12538 :=
  master scalar12538 dsL tp12538 tm12538 ep12538 em12538
    (by norm_num [dsL]) (by norm_num [tp12538]) (by norm_num [tm12538])
    (by norm_num [ep12538]) (by norm_num [em12538])
    positive12538 negative12538 tails12538.1 tails12538.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12538.1 tailGuards12538.2

theorem preserves12538 : master12538.toScalarCertificate = scalar12538 := rfl

noncomputable def tp12539 : ℝ := (2301053231 / 10000000000)
noncomputable def tm12539 : ℝ := (-((602859107 / 1000000000)))
noncomputable def ep12539 : ℝ := (50963219849214971 / 100000000000000000000)
noncomputable def em12539 : ℝ := (4970727005879859 / 10000000000000000000)
noncomputable def bp12539 : ℝ := (899750670738060397 / 2000000000000000000)
noncomputable def bm12539 : ℝ := (5735238406856822611 / 12500000000000000000)

theorem positive12539 :
    Eplus aL (agent12539.root+dsL) scalar12539.worldRadius world12539.frame
      agent12539.frame tp12539 ≤ -ep12539 := by
  apply positive_check (eT := (57771906421642963469 / 50000000000000000000)) (y := (9435273013018279327 / 25000000000000000000)) (u := (145850351527377809703 / 100000000000000000000))
  · norm_num [world12539, agent12539, scalar12539, tp12539, tm12539, ep12539, em12539, dsL]
  · norm_num [world12539, agent12539, scalar12539, tp12539, tm12539, ep12539, em12539, dsL]
  · norm_num [world12539, agent12539, scalar12539, tp12539, tm12539, ep12539, em12539, dsL]
  · norm_num [world12539, agent12539, scalar12539, tp12539, tm12539, ep12539, em12539, dsL]
  · norm_num [world12539, agent12539, scalar12539, tp12539, tm12539, ep12539, em12539, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12539, agent12539, tp12539, tm12539, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12539, agent12539, scalar12539, tp12539, tm12539, ep12539, em12539, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12539, agent12539, tp12539, tm12539, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12539, agent12539, scalar12539, tp12539, tm12539, ep12539, em12539, dsL]

theorem negative12539 :
    Eminus aL (agent12539.root+dsL) scalar12539.worldRadius world12539.frame
      agent12539.frame tm12539 ≤ -em12539 := by
  apply negative_check (lo := (68487017155470133449 / 100000000000000000000)) (hi := (1369740343109402669 / 2000000000000000000))
    (y := (-((71703018339407562757 / 100000000000000000000)))) (u := (6102499619382215427 / 12500000000000000000))
  · norm_num [world12539, agent12539, scalar12539, tp12539, tm12539, ep12539, em12539, dsL]
  · norm_num [world12539, agent12539, scalar12539, tp12539, tm12539, ep12539, em12539, dsL]
  · norm_num [world12539, agent12539, scalar12539, tp12539, tm12539, ep12539, em12539, dsL]
  · norm_num [world12539, agent12539, scalar12539, tp12539, tm12539, ep12539, em12539, dsL]
  · norm_num [world12539, agent12539, scalar12539, tp12539, tm12539, ep12539, em12539, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12539, agent12539, tp12539, tm12539, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12539, agent12539, tp12539, tm12539, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12539, agent12539, scalar12539, tp12539, tm12539, ep12539, em12539, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12539, agent12539, tp12539, tm12539, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12539, agent12539, scalar12539, tp12539, tm12539, ep12539, em12539, dsL]

theorem tails12539 :
    exp (-((12539:ℝ)*ep12539)) ≤ scalar12539.upperTail ∧
    exp (-((12539:ℝ)*em12539)) ≤ scalar12539.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12539:ℝ)) (by norm_num [ep12539]) ?_)
      (show bp12539^8 ≤ scalar12539.upperTail by norm_num [bp12539, scalar12539])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12539, bp12539, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12539:ℝ)) (by norm_num [em12539]) ?_)
      (show bm12539^8 ≤ scalar12539.lowerTail by norm_num [bm12539, scalar12539])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12539, bm12539, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12539 :
    agent12539.root+dsL+scalar12539.worldRadius < √(1/100/aL) ∧
    2*(agent12539.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12539, agent12539, scalar12539, tp12539, tm12539, ep12539, em12539, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12539, agent12539, scalar12539, tp12539, tm12539, ep12539, em12539, dsL]

noncomputable def master12539 : MasterCertificate 12539 world12539 agent12539 :=
  master scalar12539 dsL tp12539 tm12539 ep12539 em12539
    (by norm_num [dsL]) (by norm_num [tp12539]) (by norm_num [tm12539])
    (by norm_num [ep12539]) (by norm_num [em12539])
    positive12539 negative12539 tails12539.1 tails12539.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12539.1 tailGuards12539.2

theorem preserves12539 : master12539.toScalarCertificate = scalar12539 := rfl

noncomputable def tp12540 : ℝ := (287652429 / 1250000000)
noncomputable def tm12540 : ℝ := (-((6029015123 / 10000000000)))
noncomputable def ep12540 : ℝ := (50967472711638443 / 100000000000000000000)
noncomputable def em12540 : ℝ := (24855632511565079 / 50000000000000000000)
noncomputable def bp12540 : ℝ := (11245417250114790699 / 25000000000000000000)
noncomputable def bm12540 : ℝ := (5734522950938517791 / 12500000000000000000)

theorem positive12540 :
    Eplus aL (agent12540.root+dsL) scalar12540.worldRadius world12540.frame
      agent12540.frame tp12540 ≤ -ep12540 := by
  apply positive_check (eT := (115544640845459229491 / 100000000000000000000)) (y := (18870604703477786723 / 50000000000000000000)) (u := (145850522689986840341 / 100000000000000000000))
  · norm_num [world12540, agent12540, scalar12540, tp12540, tm12540, ep12540, em12540, dsL]
  · norm_num [world12540, agent12540, scalar12540, tp12540, tm12540, ep12540, em12540, dsL]
  · norm_num [world12540, agent12540, scalar12540, tp12540, tm12540, ep12540, em12540, dsL]
  · norm_num [world12540, agent12540, scalar12540, tp12540, tm12540, ep12540, em12540, dsL]
  · norm_num [world12540, agent12540, scalar12540, tp12540, tm12540, ep12540, em12540, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12540, agent12540, tp12540, tm12540, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12540, agent12540, scalar12540, tp12540, tm12540, ep12540, em12540, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12540, agent12540, tp12540, tm12540, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12540, agent12540, scalar12540, tp12540, tm12540, ep12540, em12540, dsL]

theorem negative12540 :
    Eminus aL (agent12540.root+dsL) scalar12540.worldRadius world12540.frame
      agent12540.frame tm12540 ≤ -em12540 := by
  apply negative_check (lo := (13697156057329725433 / 20000000000000000000)) (hi := (34242890143324313583 / 50000000000000000000))
    (y := (-((35850614232245841059 / 50000000000000000000)))) (u := (4882087077975731691 / 10000000000000000000))
  · norm_num [world12540, agent12540, scalar12540, tp12540, tm12540, ep12540, em12540, dsL]
  · norm_num [world12540, agent12540, scalar12540, tp12540, tm12540, ep12540, em12540, dsL]
  · norm_num [world12540, agent12540, scalar12540, tp12540, tm12540, ep12540, em12540, dsL]
  · norm_num [world12540, agent12540, scalar12540, tp12540, tm12540, ep12540, em12540, dsL]
  · norm_num [world12540, agent12540, scalar12540, tp12540, tm12540, ep12540, em12540, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12540, agent12540, tp12540, tm12540, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12540, agent12540, tp12540, tm12540, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12540, agent12540, scalar12540, tp12540, tm12540, ep12540, em12540, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12540, agent12540, tp12540, tm12540, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12540, agent12540, scalar12540, tp12540, tm12540, ep12540, em12540, dsL]

theorem tails12540 :
    exp (-((12540:ℝ)*ep12540)) ≤ scalar12540.upperTail ∧
    exp (-((12540:ℝ)*em12540)) ≤ scalar12540.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12540:ℝ)) (by norm_num [ep12540]) ?_)
      (show bp12540^8 ≤ scalar12540.upperTail by norm_num [bp12540, scalar12540])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12540, bp12540, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12540:ℝ)) (by norm_num [em12540]) ?_)
      (show bm12540^8 ≤ scalar12540.lowerTail by norm_num [bm12540, scalar12540])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12540, bm12540, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12540 :
    agent12540.root+dsL+scalar12540.worldRadius < √(1/100/aL) ∧
    2*(agent12540.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12540, agent12540, scalar12540, tp12540, tm12540, ep12540, em12540, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12540, agent12540, scalar12540, tp12540, tm12540, ep12540, em12540, dsL]

noncomputable def master12540 : MasterCertificate 12540 world12540 agent12540 :=
  master scalar12540 dsL tp12540 tm12540 ep12540 em12540
    (by norm_num [dsL]) (by norm_num [tp12540]) (by norm_num [tm12540])
    (by norm_num [ep12540]) (by norm_num [em12540])
    positive12540 negative12540 tails12540.1 tails12540.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12540.1 tailGuards12540.2

theorem preserves12540 : master12540.toScalarCertificate = scalar12540 := rfl

noncomputable def tp12541 : ℝ := (1150654917 / 5000000000)
noncomputable def tm12541 : ℝ := (-((1205842013 / 2000000000)))
noncomputable def ep12541 : ℝ := (25485134447701863 / 50000000000000000000)
noncomputable def em12541 : ℝ := (49713674955361023 / 100000000000000000000)
noncomputable def bp12541 : ℝ := (44976831796189780163 / 100000000000000000000)
noncomputable def bm12541 : ℝ := (45871599990018642811 / 100000000000000000000)

theorem positive12541 :
    Eplus aL (agent12541.root+dsL) scalar12541.worldRadius world12541.frame
      agent12541.frame tp12541 ≤ -ep12541 := by
  apply positive_check (eT := (28886229742714190851 / 25000000000000000000)) (y := (18871028675868299197 / 50000000000000000000)) (u := (145851759427125504293 / 100000000000000000000))
  · norm_num [world12541, agent12541, scalar12541, tp12541, tm12541, ep12541, em12541, dsL]
  · norm_num [world12541, agent12541, scalar12541, tp12541, tm12541, ep12541, em12541, dsL]
  · norm_num [world12541, agent12541, scalar12541, tp12541, tm12541, ep12541, em12541, dsL]
  · norm_num [world12541, agent12541, scalar12541, tp12541, tm12541, ep12541, em12541, dsL]
  · norm_num [world12541, agent12541, scalar12541, tp12541, tm12541, ep12541, em12541, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12541, agent12541, tp12541, tm12541, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12541, agent12541, scalar12541, tp12541, tm12541, ep12541, em12541, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12541, agent12541, tp12541, tm12541, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12541, agent12541, scalar12541, tp12541, tm12541, ep12541, em12541, dsL]

theorem negative12541 :
    Eminus aL (agent12541.root+dsL) scalar12541.worldRadius world12541.frame
      agent12541.frame tm12541 ≤ -em12541 := by
  apply negative_check (lo := (2739421143037606547 / 4000000000000000000)) (hi := (17121382143985040919 / 25000000000000000000))
    (y := (-((71701365056167600027 / 100000000000000000000)))) (u := (976416081891145287 / 2000000000000000000))
  · norm_num [world12541, agent12541, scalar12541, tp12541, tm12541, ep12541, em12541, dsL]
  · norm_num [world12541, agent12541, scalar12541, tp12541, tm12541, ep12541, em12541, dsL]
  · norm_num [world12541, agent12541, scalar12541, tp12541, tm12541, ep12541, em12541, dsL]
  · norm_num [world12541, agent12541, scalar12541, tp12541, tm12541, ep12541, em12541, dsL]
  · norm_num [world12541, agent12541, scalar12541, tp12541, tm12541, ep12541, em12541, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12541, agent12541, tp12541, tm12541, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12541, agent12541, tp12541, tm12541, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12541, agent12541, scalar12541, tp12541, tm12541, ep12541, em12541, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12541, agent12541, tp12541, tm12541, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12541, agent12541, scalar12541, tp12541, tm12541, ep12541, em12541, dsL]

theorem tails12541 :
    exp (-((12541:ℝ)*ep12541)) ≤ scalar12541.upperTail ∧
    exp (-((12541:ℝ)*em12541)) ≤ scalar12541.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12541:ℝ)) (by norm_num [ep12541]) ?_)
      (show bp12541^8 ≤ scalar12541.upperTail by norm_num [bp12541, scalar12541])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12541, bp12541, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12541:ℝ)) (by norm_num [em12541]) ?_)
      (show bm12541^8 ≤ scalar12541.lowerTail by norm_num [bm12541, scalar12541])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12541, bm12541, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12541 :
    agent12541.root+dsL+scalar12541.worldRadius < √(1/100/aL) ∧
    2*(agent12541.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12541, agent12541, scalar12541, tp12541, tm12541, ep12541, em12541, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12541, agent12541, scalar12541, tp12541, tm12541, ep12541, em12541, dsL]

noncomputable def master12541 : MasterCertificate 12541 world12541 agent12541 :=
  master scalar12541 dsL tp12541 tm12541 ep12541 em12541
    (by norm_num [dsL]) (by norm_num [tp12541]) (by norm_num [tm12541])
    (by norm_num [ep12541]) (by norm_num [em12541])
    positive12541 negative12541 tails12541.1 tails12541.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12541.1 tailGuards12541.2

theorem preserves12541 : master12541.toScalarCertificate = scalar12541 := rfl

noncomputable def tp12542 : ℝ := (1150700107 / 5000000000)
noncomputable def tm12542 : ℝ := (-((6029404947 / 10000000000)))
noncomputable def ep12542 : ℝ := (50973064107786299 / 100000000000000000000)
noncomputable def em12542 : ℝ := (9943216795142821 / 20000000000000000000)
noncomputable def bp12542 : ℝ := (44971995482596937703 / 100000000000000000000)
noncomputable def bm12542 : ℝ := (22933508604931684451 / 50000000000000000000)

theorem positive12542 :
    Eplus aL (agent12542.root+dsL) scalar12542.worldRadius world12542.frame
      agent12542.frame tp12542 ≤ -ep12542 := by
  apply positive_check (eT := (115545196969183999443 / 100000000000000000000)) (y := (37742905361310694307 / 100000000000000000000)) (u := (36463249067313424019 / 25000000000000000000))
  · norm_num [world12542, agent12542, scalar12542, tp12542, tm12542, ep12542, em12542, dsL]
  · norm_num [world12542, agent12542, scalar12542, tp12542, tm12542, ep12542, em12542, dsL]
  · norm_num [world12542, agent12542, scalar12542, tp12542, tm12542, ep12542, em12542, dsL]
  · norm_num [world12542, agent12542, scalar12542, tp12542, tm12542, ep12542, em12542, dsL]
  · norm_num [world12542, agent12542, scalar12542, tp12542, tm12542, ep12542, em12542, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12542, agent12542, tp12542, tm12542, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12542, agent12542, scalar12542, tp12542, tm12542, ep12542, em12542, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12542, agent12542, tp12542, tm12542, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12542, agent12542, scalar12542, tp12542, tm12542, ep12542, em12542, dsL]

theorem negative12542 :
    Eminus aL (agent12542.root+dsL) scalar12542.worldRadius world12542.frame
      agent12542.frame tm12542 ≤ -em12542 := by
  apply negative_check (lo := (17121319266630634947 / 25000000000000000000)) (hi := (68485277066522539789 / 100000000000000000000))
    (y := (-((7170150210085824211 / 10000000000000000000)))) (u := (9764147437656633949 / 20000000000000000000))
  · norm_num [world12542, agent12542, scalar12542, tp12542, tm12542, ep12542, em12542, dsL]
  · norm_num [world12542, agent12542, scalar12542, tp12542, tm12542, ep12542, em12542, dsL]
  · norm_num [world12542, agent12542, scalar12542, tp12542, tm12542, ep12542, em12542, dsL]
  · norm_num [world12542, agent12542, scalar12542, tp12542, tm12542, ep12542, em12542, dsL]
  · norm_num [world12542, agent12542, scalar12542, tp12542, tm12542, ep12542, em12542, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12542, agent12542, tp12542, tm12542, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12542, agent12542, tp12542, tm12542, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12542, agent12542, scalar12542, tp12542, tm12542, ep12542, em12542, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12542, agent12542, tp12542, tm12542, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12542, agent12542, scalar12542, tp12542, tm12542, ep12542, em12542, dsL]

theorem tails12542 :
    exp (-((12542:ℝ)*ep12542)) ≤ scalar12542.upperTail ∧
    exp (-((12542:ℝ)*em12542)) ≤ scalar12542.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12542:ℝ)) (by norm_num [ep12542]) ?_)
      (show bp12542^8 ≤ scalar12542.upperTail by norm_num [bp12542, scalar12542])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12542, bp12542, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12542:ℝ)) (by norm_num [em12542]) ?_)
      (show bm12542^8 ≤ scalar12542.lowerTail by norm_num [bm12542, scalar12542])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12542, bm12542, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12542 :
    agent12542.root+dsL+scalar12542.worldRadius < √(1/100/aL) ∧
    2*(agent12542.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12542, agent12542, scalar12542, tp12542, tm12542, ep12542, em12542, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12542, agent12542, scalar12542, tp12542, tm12542, ep12542, em12542, dsL]

noncomputable def master12542 : MasterCertificate 12542 world12542 agent12542 :=
  master scalar12542 dsL tp12542 tm12542 ep12542 em12542
    (by norm_num [dsL]) (by norm_num [tp12542]) (by norm_num [tm12542])
    (by norm_num [ep12542]) (by norm_num [em12542])
    positive12542 negative12542 tails12542.1 tails12542.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12542.1 tailGuards12542.2

theorem preserves12542 : master12542.toScalarCertificate = scalar12542 := rfl

noncomputable def tp12543 : ℝ := (1150745241 / 5000000000)
noncomputable def tm12543 : ℝ := (-((1507399889 / 2500000000)))
noncomputable def ep12543 : ℝ := (6371982135539811 / 12500000000000000000)
noncomputable def em12543 : ℝ := (9943698186332999 / 20000000000000000000)
noncomputable def bp12543 : ℝ := (5620895118894399123 / 12500000000000000000)
noncomputable def bm12543 : ℝ := (45862436095780418639 / 100000000000000000000)

theorem positive12543 :
    Eplus aL (agent12543.root+dsL) scalar12543.worldRadius world12543.frame
      agent12543.frame tp12543 ≤ -ep12543 := by
  apply positive_check (eT := (23109094837509500421 / 20000000000000000000)) (y := (4717968980629814103 / 12500000000000000000)) (u := (72927115448179551229 / 50000000000000000000))
  · norm_num [world12543, agent12543, scalar12543, tp12543, tm12543, ep12543, em12543, dsL]
  · norm_num [world12543, agent12543, scalar12543, tp12543, tm12543, ep12543, em12543, dsL]
  · norm_num [world12543, agent12543, scalar12543, tp12543, tm12543, ep12543, em12543, dsL]
  · norm_num [world12543, agent12543, scalar12543, tp12543, tm12543, ep12543, em12543, dsL]
  · norm_num [world12543, agent12543, scalar12543, tp12543, tm12543, ep12543, em12543, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12543, agent12543, tp12543, tm12543, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12543, agent12543, scalar12543, tp12543, tm12543, ep12543, em12543, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12543, agent12543, tp12543, tm12543, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12543, agent12543, scalar12543, tp12543, tm12543, ep12543, em12543, dsL]

theorem negative12543 :
    Eminus aL (agent12543.root+dsL) scalar12543.worldRadius world12543.frame
      agent12543.frame tm12543 ≤ -em12543 := by
  apply negative_check (lo := (34242513337120025569 / 50000000000000000000)) (hi := (68485026674240051139 / 100000000000000000000))
    (y := (-((17925409210407303377 / 25000000000000000000)))) (u := (610258392586122569 / 1250000000000000000))
  · norm_num [world12543, agent12543, scalar12543, tp12543, tm12543, ep12543, em12543, dsL]
  · norm_num [world12543, agent12543, scalar12543, tp12543, tm12543, ep12543, em12543, dsL]
  · norm_num [world12543, agent12543, scalar12543, tp12543, tm12543, ep12543, em12543, dsL]
  · norm_num [world12543, agent12543, scalar12543, tp12543, tm12543, ep12543, em12543, dsL]
  · norm_num [world12543, agent12543, scalar12543, tp12543, tm12543, ep12543, em12543, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12543, agent12543, tp12543, tm12543, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12543, agent12543, tp12543, tm12543, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12543, agent12543, scalar12543, tp12543, tm12543, ep12543, em12543, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12543, agent12543, tp12543, tm12543, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12543, agent12543, scalar12543, tp12543, tm12543, ep12543, em12543, dsL]

theorem tails12543 :
    exp (-((12543:ℝ)*ep12543)) ≤ scalar12543.upperTail ∧
    exp (-((12543:ℝ)*em12543)) ≤ scalar12543.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12543:ℝ)) (by norm_num [ep12543]) ?_)
      (show bp12543^8 ≤ scalar12543.upperTail by norm_num [bp12543, scalar12543])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12543, bp12543, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12543:ℝ)) (by norm_num [em12543]) ?_)
      (show bm12543^8 ≤ scalar12543.lowerTail by norm_num [bm12543, scalar12543])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12543, bm12543, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12543 :
    agent12543.root+dsL+scalar12543.worldRadius < √(1/100/aL) ∧
    2*(agent12543.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12543, agent12543, scalar12543, tp12543, tm12543, ep12543, em12543, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12543, agent12543, scalar12543, tp12543, tm12543, ep12543, em12543, dsL]

noncomputable def master12543 : MasterCertificate 12543 world12543 agent12543 :=
  master scalar12543 dsL tp12543 tm12543 ep12543 em12543
    (by norm_num [dsL]) (by norm_num [tp12543]) (by norm_num [tm12543])
    (by norm_num [ep12543]) (by norm_num [em12543])
    positive12543 negative12543 tails12543.1 tails12543.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12543.1 tailGuards12543.2

theorem preserves12543 : master12543.toScalarCertificate = scalar12543 := rfl

noncomputable def tp12544 : ℝ := (143848791 / 625000000)
noncomputable def tm12544 : ℝ := (-((3014897109 / 5000000000)))
noncomputable def ep12544 : ℝ := (50978648296860183 / 100000000000000000000)
noncomputable def em12544 : ℝ := (4972089626594457 / 10000000000000000000)
noncomputable def bp12544 : ℝ := (44962327869112964569 / 100000000000000000000)
noncomputable def bm12544 : ℝ := (22928928164685434417 / 50000000000000000000)

theorem positive12544 :
    Eplus aL (agent12544.root+dsL) scalar12544.worldRadius world12544.frame
      agent12544.frame tp12544 ≤ -ep12544 := by
  apply positive_check (eT := (28886437689144545459 / 25000000000000000000)) (y := (37744597172896009759 / 100000000000000000000)) (u := (145855463848015441851 / 100000000000000000000))
  · norm_num [world12544, agent12544, scalar12544, tp12544, tm12544, ep12544, em12544, dsL]
  · norm_num [world12544, agent12544, scalar12544, tp12544, tm12544, ep12544, em12544, dsL]
  · norm_num [world12544, agent12544, scalar12544, tp12544, tm12544, ep12544, em12544, dsL]
  · norm_num [world12544, agent12544, scalar12544, tp12544, tm12544, ep12544, em12544, dsL]
  · norm_num [world12544, agent12544, scalar12544, tp12544, tm12544, ep12544, em12544, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12544, agent12544, tp12544, tm12544, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12544, agent12544, scalar12544, tp12544, tm12544, ep12544, em12544, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12544, agent12544, tp12544, tm12544, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12544, agent12544, scalar12544, tp12544, tm12544, ep12544, em12544, dsL]

theorem negative12544 :
    Eminus aL (agent12544.root+dsL) scalar12544.worldRadius world12544.frame
      agent12544.frame tm12544 ≤ -em12544 := by
  apply negative_check (lo := (6848477599733245701 / 10000000000000000000)) (hi := (68484775997332457011 / 100000000000000000000))
    (y := (-((71701773008523870691 / 100000000000000000000)))) (u := (48820604929342860187 / 100000000000000000000))
  · norm_num [world12544, agent12544, scalar12544, tp12544, tm12544, ep12544, em12544, dsL]
  · norm_num [world12544, agent12544, scalar12544, tp12544, tm12544, ep12544, em12544, dsL]
  · norm_num [world12544, agent12544, scalar12544, tp12544, tm12544, ep12544, em12544, dsL]
  · norm_num [world12544, agent12544, scalar12544, tp12544, tm12544, ep12544, em12544, dsL]
  · norm_num [world12544, agent12544, scalar12544, tp12544, tm12544, ep12544, em12544, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12544, agent12544, tp12544, tm12544, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12544, agent12544, tp12544, tm12544, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12544, agent12544, scalar12544, tp12544, tm12544, ep12544, em12544, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12544, agent12544, tp12544, tm12544, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12544, agent12544, scalar12544, tp12544, tm12544, ep12544, em12544, dsL]

theorem tails12544 :
    exp (-((12544:ℝ)*ep12544)) ≤ scalar12544.upperTail ∧
    exp (-((12544:ℝ)*em12544)) ≤ scalar12544.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12544:ℝ)) (by norm_num [ep12544]) ?_)
      (show bp12544^8 ≤ scalar12544.upperTail by norm_num [bp12544, scalar12544])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12544, bp12544, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12544:ℝ)) (by norm_num [em12544]) ?_)
      (show bm12544^8 ≤ scalar12544.lowerTail by norm_num [bm12544, scalar12544])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12544, bm12544, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12544 :
    agent12544.root+dsL+scalar12544.worldRadius < √(1/100/aL) ∧
    2*(agent12544.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12544, agent12544, scalar12544, tp12544, tm12544, ep12544, em12544, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12544, agent12544, scalar12544, tp12544, tm12544, ep12544, em12544, dsL]

noncomputable def master12544 : MasterCertificate 12544 world12544 agent12544 :=
  master scalar12544 dsL tp12544 tm12544 ep12544 em12544
    (by norm_num [dsL]) (by norm_num [tp12544]) (by norm_num [tm12544])
    (by norm_num [ep12544]) (by norm_num [em12544])
    positive12544 negative12544 tails12544.1 tails12544.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12544.1 tailGuards12544.2

theorem preserves12544 : master12544.toScalarCertificate = scalar12544 := rfl

noncomputable def tp12545 : ℝ := (2301670893 / 10000000000)
noncomputable def tm12545 : ℝ := (-((3014994397 / 5000000000)))
noncomputable def ep12545 : ℝ := (5098143917725161 / 10000000000000000000)
noncomputable def em12545 : ℝ := (6215412654243281 / 12500000000000000000)
noncomputable def bp12545 : ℝ := (22478747613489676377 / 50000000000000000000)
noncomputable def bm12545 : ℝ := (22926638503963628793 / 50000000000000000000)

theorem positive12545 :
    Eplus aL (agent12545.root+dsL) scalar12545.worldRadius world12545.frame
      agent12545.frame tp12545 ≤ -ep12545 := by
  apply positive_check (eT := (115546027815198677069 / 100000000000000000000)) (y := (9436361015977698731 / 25000000000000000000)) (u := (29171339818012782699 / 20000000000000000000))
  · norm_num [world12545, agent12545, scalar12545, tp12545, tm12545, ep12545, em12545, dsL]
  · norm_num [world12545, agent12545, scalar12545, tp12545, tm12545, ep12545, em12545, dsL]
  · norm_num [world12545, agent12545, scalar12545, tp12545, tm12545, ep12545, em12545, dsL]
  · norm_num [world12545, agent12545, scalar12545, tp12545, tm12545, ep12545, em12545, dsL]
  · norm_num [world12545, agent12545, scalar12545, tp12545, tm12545, ep12545, em12545, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12545, agent12545, tp12545, tm12545, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12545, agent12545, scalar12545, tp12545, tm12545, ep12545, em12545, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12545, agent12545, tp12545, tm12545, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12545, agent12545, scalar12545, tp12545, tm12545, ep12545, em12545, dsL]

theorem negative12545 :
    Eminus aL (agent12545.root+dsL) scalar12545.worldRadius world12545.frame
      agent12545.frame tm12545 ≤ -em12545 := by
  apply negative_check (lo := (68484525633433314413 / 100000000000000000000)) (hi := (34242262816716657207 / 50000000000000000000))
    (y := (-((71701909379238091827 / 100000000000000000000)))) (u := (48820538352380626713 / 100000000000000000000))
  · norm_num [world12545, agent12545, scalar12545, tp12545, tm12545, ep12545, em12545, dsL]
  · norm_num [world12545, agent12545, scalar12545, tp12545, tm12545, ep12545, em12545, dsL]
  · norm_num [world12545, agent12545, scalar12545, tp12545, tm12545, ep12545, em12545, dsL]
  · norm_num [world12545, agent12545, scalar12545, tp12545, tm12545, ep12545, em12545, dsL]
  · norm_num [world12545, agent12545, scalar12545, tp12545, tm12545, ep12545, em12545, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12545, agent12545, tp12545, tm12545, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12545, agent12545, tp12545, tm12545, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12545, agent12545, scalar12545, tp12545, tm12545, ep12545, em12545, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12545, agent12545, tp12545, tm12545, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12545, agent12545, scalar12545, tp12545, tm12545, ep12545, em12545, dsL]

theorem tails12545 :
    exp (-((12545:ℝ)*ep12545)) ≤ scalar12545.upperTail ∧
    exp (-((12545:ℝ)*em12545)) ≤ scalar12545.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12545:ℝ)) (by norm_num [ep12545]) ?_)
      (show bp12545^8 ≤ scalar12545.upperTail by norm_num [bp12545, scalar12545])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12545, bp12545, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12545:ℝ)) (by norm_num [em12545]) ?_)
      (show bm12545^8 ≤ scalar12545.lowerTail by norm_num [bm12545, scalar12545])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12545, bm12545, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12545 :
    agent12545.root+dsL+scalar12545.worldRadius < √(1/100/aL) ∧
    2*(agent12545.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12545, agent12545, scalar12545, tp12545, tm12545, ep12545, em12545, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12545, agent12545, scalar12545, tp12545, tm12545, ep12545, em12545, dsL]

noncomputable def master12545 : MasterCertificate 12545 world12545 agent12545 :=
  master scalar12545 dsL tp12545 tm12545 ep12545 em12545
    (by norm_num [dsL]) (by norm_num [tp12545]) (by norm_num [tm12545])
    (by norm_num [ep12545]) (by norm_num [em12545])
    positive12545 negative12545 tails12545.1 tails12545.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12545.1 tailGuards12545.2

theorem preserves12545 : master12545.toScalarCertificate = scalar12545 := rfl

noncomputable def tp12546 : ℝ := (2301761069 / 10000000000)
noncomputable def tm12546 : ℝ := (-((6030183241 / 10000000000)))
noncomputable def ep12546 : ℝ := (1274605699156647 / 2500000000000000000)
noncomputable def em12546 : ℝ := (9945140858911237 / 20000000000000000000)
noncomputable def bp12546 : ℝ := (22476332132491304043 / 50000000000000000000)
noncomputable def bm12546 : ℝ := (45848699239565688533 / 100000000000000000000)

theorem positive12546 :
    Eplus aL (agent12546.root+dsL) scalar12546.worldRadius world12546.frame
      agent12546.frame tp12546 ≤ -ep12546 := by
  apply positive_check (eT := (7221644028992976679 / 6250000000000000000)) (y := (147446446394724161 / 390625000000000000)) (u := (72928966676918685733 / 50000000000000000000))
  · norm_num [world12546, agent12546, scalar12546, tp12546, tm12546, ep12546, em12546, dsL]
  · norm_num [world12546, agent12546, scalar12546, tp12546, tm12546, ep12546, em12546, dsL]
  · norm_num [world12546, agent12546, scalar12546, tp12546, tm12546, ep12546, em12546, dsL]
  · norm_num [world12546, agent12546, scalar12546, tp12546, tm12546, ep12546, em12546, dsL]
  · norm_num [world12546, agent12546, scalar12546, tp12546, tm12546, ep12546, em12546, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12546, agent12546, tp12546, tm12546, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12546, agent12546, scalar12546, tp12546, tm12546, ep12546, em12546, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12546, agent12546, tp12546, tm12546, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12546, agent12546, scalar12546, tp12546, tm12546, ep12546, em12546, dsL]

theorem negative12546 :
    Eminus aL (agent12546.root+dsL) scalar12546.worldRadius world12546.frame
      agent12546.frame tm12546 ≤ -em12546 := by
  apply negative_check (lo := (34242137883708933917 / 50000000000000000000)) (hi := (13696855153483573567 / 20000000000000000000))
    (y := (-((35851022489288646861 / 50000000000000000000)))) (u := (2441023607604905483 / 5000000000000000000))
  · norm_num [world12546, agent12546, scalar12546, tp12546, tm12546, ep12546, em12546, dsL]
  · norm_num [world12546, agent12546, scalar12546, tp12546, tm12546, ep12546, em12546, dsL]
  · norm_num [world12546, agent12546, scalar12546, tp12546, tm12546, ep12546, em12546, dsL]
  · norm_num [world12546, agent12546, scalar12546, tp12546, tm12546, ep12546, em12546, dsL]
  · norm_num [world12546, agent12546, scalar12546, tp12546, tm12546, ep12546, em12546, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12546, agent12546, tp12546, tm12546, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12546, agent12546, tp12546, tm12546, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12546, agent12546, scalar12546, tp12546, tm12546, ep12546, em12546, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12546, agent12546, tp12546, tm12546, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12546, agent12546, scalar12546, tp12546, tm12546, ep12546, em12546, dsL]

theorem tails12546 :
    exp (-((12546:ℝ)*ep12546)) ≤ scalar12546.upperTail ∧
    exp (-((12546:ℝ)*em12546)) ≤ scalar12546.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12546:ℝ)) (by norm_num [ep12546]) ?_)
      (show bp12546^8 ≤ scalar12546.upperTail by norm_num [bp12546, scalar12546])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12546, bp12546, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12546:ℝ)) (by norm_num [em12546]) ?_)
      (show bm12546^8 ≤ scalar12546.lowerTail by norm_num [bm12546, scalar12546])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12546, bm12546, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12546 :
    agent12546.root+dsL+scalar12546.worldRadius < √(1/100/aL) ∧
    2*(agent12546.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12546, agent12546, scalar12546, tp12546, tm12546, ep12546, em12546, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12546, agent12546, scalar12546, tp12546, tm12546, ep12546, em12546, dsL]

noncomputable def master12546 : MasterCertificate 12546 world12546 agent12546 :=
  master scalar12546 dsL tp12546 tm12546 ep12546 em12546
    (by norm_num [dsL]) (by norm_num [tp12546]) (by norm_num [tm12546])
    (by norm_num [ep12546]) (by norm_num [em12546])
    positive12546 negative12546 tails12546.1 tails12546.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12546.1 tailGuards12546.2

theorem preserves12546 : master12546.toScalarCertificate = scalar12546 := rfl

noncomputable def tp12547 : ℝ := (2301851161 / 10000000000)
noncomputable def tm12547 : ℝ := (-((1206075511 / 2000000000)))
noncomputable def ep12547 : ℝ := (25493507894454967 / 50000000000000000000)
noncomputable def em12547 : ℝ := (12432026611958729 / 25000000000000000000)
noncomputable def bp12547 : ℝ := (22473917094985457977 / 50000000000000000000)
noncomputable def bm12547 : ℝ := (22922061152594463479 / 50000000000000000000)

theorem positive12547 :
    Eplus aL (agent12547.root+dsL) scalar12547.worldRadius world12547.frame
      agent12547.frame tp12547 ≤ -ep12547 := by
  apply positive_check (eT := (115546580535791486173 / 100000000000000000000)) (y := (18873567731013726803 / 50000000000000000000)) (u := (145859166128389004427 / 100000000000000000000))
  · norm_num [world12547, agent12547, scalar12547, tp12547, tm12547, ep12547, em12547, dsL]
  · norm_num [world12547, agent12547, scalar12547, tp12547, tm12547, ep12547, em12547, dsL]
  · norm_num [world12547, agent12547, scalar12547, tp12547, tm12547, ep12547, em12547, dsL]
  · norm_num [world12547, agent12547, scalar12547, tp12547, tm12547, ep12547, em12547, dsL]
  · norm_num [world12547, agent12547, scalar12547, tp12547, tm12547, ep12547, em12547, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12547, agent12547, tp12547, tm12547, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12547, agent12547, scalar12547, tp12547, tm12547, ep12547, em12547, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12547, agent12547, tp12547, tm12547, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12547, agent12547, scalar12547, tp12547, tm12547, ep12547, em12547, dsL]

theorem negative12547 :
    Eminus aL (agent12547.root+dsL) scalar12547.worldRadius world12547.frame
      agent12547.frame tm12547 ≤ -em12547 := by
  apply negative_check (lo := (8560503302064166761 / 12500000000000000000)) (hi := (68484026416513334089 / 100000000000000000000))
    (y := (-((71702180314911433189 / 100000000000000000000)))) (u := (12205101520076374753 / 25000000000000000000))
  · norm_num [world12547, agent12547, scalar12547, tp12547, tm12547, ep12547, em12547, dsL]
  · norm_num [world12547, agent12547, scalar12547, tp12547, tm12547, ep12547, em12547, dsL]
  · norm_num [world12547, agent12547, scalar12547, tp12547, tm12547, ep12547, em12547, dsL]
  · norm_num [world12547, agent12547, scalar12547, tp12547, tm12547, ep12547, em12547, dsL]
  · norm_num [world12547, agent12547, scalar12547, tp12547, tm12547, ep12547, em12547, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12547, agent12547, tp12547, tm12547, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12547, agent12547, tp12547, tm12547, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12547, agent12547, scalar12547, tp12547, tm12547, ep12547, em12547, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12547, agent12547, tp12547, tm12547, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12547, agent12547, scalar12547, tp12547, tm12547, ep12547, em12547, dsL]

theorem tails12547 :
    exp (-((12547:ℝ)*ep12547)) ≤ scalar12547.upperTail ∧
    exp (-((12547:ℝ)*em12547)) ≤ scalar12547.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12547:ℝ)) (by norm_num [ep12547]) ?_)
      (show bp12547^8 ≤ scalar12547.upperTail by norm_num [bp12547, scalar12547])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12547, bp12547, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12547:ℝ)) (by norm_num [em12547]) ?_)
      (show bm12547^8 ≤ scalar12547.lowerTail by norm_num [bm12547, scalar12547])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12547, bm12547, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12547 :
    agent12547.root+dsL+scalar12547.worldRadius < √(1/100/aL) ∧
    2*(agent12547.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12547, agent12547, scalar12547, tp12547, tm12547, ep12547, em12547, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12547, agent12547, scalar12547, tp12547, tm12547, ep12547, em12547, dsL]

noncomputable def master12547 : MasterCertificate 12547 world12547 agent12547 :=
  master scalar12547 dsL tp12547 tm12547 ep12547 em12547
    (by norm_num [dsL]) (by norm_num [tp12547]) (by norm_num [tm12547])
    (by norm_num [ep12547]) (by norm_num [em12547])
    positive12547 negative12547 tails12547.1 tails12547.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12547.1 tailGuards12547.2

theorem preserves12547 : master12547.toScalarCertificate = scalar12547 := rfl

noncomputable def tp12548 : ℝ := (1150970627 / 5000000000)
noncomputable def tm12548 : ℝ := (-((3015285947 / 5000000000)))
noncomputable def ep12548 : ℝ := (12747450661326549 / 25000000000000000000)
noncomputable def em12548 : ℝ := (49730507864256531 / 100000000000000000000)
noncomputable def bp12548 : ℝ := (44943005001846481847 / 100000000000000000000)
noncomputable def bm12548 : ℝ := (45839546082224696279 / 100000000000000000000)

theorem positive12548 :
    Eplus aL (agent12548.root+dsL) scalar12548.worldRadius world12548.frame
      agent12548.frame tp12548 ≤ -ep12548 := by
  apply positive_check (eT := (57773428323779096397 / 50000000000000000000)) (y := (37747979746303329081 / 100000000000000000000)) (u := (36465099399898025263 / 25000000000000000000))
  · norm_num [world12548, agent12548, scalar12548, tp12548, tm12548, ep12548, em12548, dsL]
  · norm_num [world12548, agent12548, scalar12548, tp12548, tm12548, ep12548, em12548, dsL]
  · norm_num [world12548, agent12548, scalar12548, tp12548, tm12548, ep12548, em12548, dsL]
  · norm_num [world12548, agent12548, scalar12548, tp12548, tm12548, ep12548, em12548, dsL]
  · norm_num [world12548, agent12548, scalar12548, tp12548, tm12548, ep12548, em12548, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12548, agent12548, tp12548, tm12548, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12548, agent12548, scalar12548, tp12548, tm12548, ep12548, em12548, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12548, agent12548, tp12548, tm12548, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12548, agent12548, scalar12548, tp12548, tm12548, ep12548, em12548, dsL]

theorem negative12548 :
    Eminus aL (agent12548.root+dsL) scalar12548.worldRadius world12548.frame
      agent12548.frame tm12548 ≤ -em12548 := by
  apply negative_check (lo := (4280236056332695331 / 6250000000000000000)) (hi := (68483776901323125297 / 100000000000000000000))
    (y := (-((35851156834583116727 / 50000000000000000000)))) (u := (1952813639050407587 / 4000000000000000000))
  · norm_num [world12548, agent12548, scalar12548, tp12548, tm12548, ep12548, em12548, dsL]
  · norm_num [world12548, agent12548, scalar12548, tp12548, tm12548, ep12548, em12548, dsL]
  · norm_num [world12548, agent12548, scalar12548, tp12548, tm12548, ep12548, em12548, dsL]
  · norm_num [world12548, agent12548, scalar12548, tp12548, tm12548, ep12548, em12548, dsL]
  · norm_num [world12548, agent12548, scalar12548, tp12548, tm12548, ep12548, em12548, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12548, agent12548, tp12548, tm12548, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12548, agent12548, tp12548, tm12548, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12548, agent12548, scalar12548, tp12548, tm12548, ep12548, em12548, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12548, agent12548, tp12548, tm12548, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12548, agent12548, scalar12548, tp12548, tm12548, ep12548, em12548, dsL]

theorem tails12548 :
    exp (-((12548:ℝ)*ep12548)) ≤ scalar12548.upperTail ∧
    exp (-((12548:ℝ)*em12548)) ≤ scalar12548.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12548:ℝ)) (by norm_num [ep12548]) ?_)
      (show bp12548^8 ≤ scalar12548.upperTail by norm_num [bp12548, scalar12548])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12548, bp12548, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12548:ℝ)) (by norm_num [em12548]) ?_)
      (show bm12548^8 ≤ scalar12548.lowerTail by norm_num [bm12548, scalar12548])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12548, bm12548, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12548 :
    agent12548.root+dsL+scalar12548.worldRadius < √(1/100/aL) ∧
    2*(agent12548.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12548, agent12548, scalar12548, tp12548, tm12548, ep12548, em12548, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12548, agent12548, scalar12548, tp12548, tm12548, ep12548, em12548, dsL]

noncomputable def master12548 : MasterCertificate 12548 world12548 agent12548 :=
  master scalar12548 dsL tp12548 tm12548 ep12548 em12548
    (by norm_num [dsL]) (by norm_num [tp12548]) (by norm_num [tm12548])
    (by norm_num [ep12548]) (by norm_num [em12548])
    positive12548 negative12548 tails12548.1 tails12548.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12548.1 tailGuards12548.2

theorem preserves12548 : master12548.toScalarCertificate = scalar12548 := rfl

noncomputable def tp12549 : ℝ := (1151015807 / 5000000000)
noncomputable def tm12549 : ℝ := (-((241230677 / 400000000)))
noncomputable def ep12549 : ℝ := (25496296877569861 / 50000000000000000000)
noncomputable def em12549 : ℝ := (49732914000778511 / 100000000000000000000)
noncomputable def bp12549 : ℝ := (22469086510591026009 / 50000000000000000000)
noncomputable def bm12549 : ℝ := (22917483323620604031 / 50000000000000000000)

theorem positive12549 :
    Eplus aL (agent12549.root+dsL) scalar12549.worldRadius world12549.frame
      agent12549.frame tp12549 ≤ -ep12549 := by
  apply positive_check (eT := (115547134728515888353 / 100000000000000000000)) (y := (18874411103016831143 / 50000000000000000000)) (u := (36465406604970133073 / 25000000000000000000))
  · norm_num [world12549, agent12549, scalar12549, tp12549, tm12549, ep12549, em12549, dsL]
  · norm_num [world12549, agent12549, scalar12549, tp12549, tm12549, ep12549, em12549, dsL]
  · norm_num [world12549, agent12549, scalar12549, tp12549, tm12549, ep12549, em12549, dsL]
  · norm_num [world12549, agent12549, scalar12549, tp12549, tm12549, ep12549, em12549, dsL]
  · norm_num [world12549, agent12549, scalar12549, tp12549, tm12549, ep12549, em12549, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12549, agent12549, tp12549, tm12549, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12549, agent12549, scalar12549, tp12549, tm12549, ep12549, em12549, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12549, agent12549, tp12549, tm12549, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12549, agent12549, scalar12549, tp12549, tm12549, ep12549, em12549, dsL]

theorem negative12549 :
    Eminus aL (agent12549.root+dsL) scalar12549.worldRadius world12549.frame
      agent12549.frame tm12549 ≤ -em12549 := by
  apply negative_check (lo := (13696704870907157087 / 20000000000000000000)) (hi := (17120881088633946359 / 25000000000000000000))
    (y := (-((71702440912055463297 / 100000000000000000000)))) (u := (48820278855887321507 / 100000000000000000000))
  · norm_num [world12549, agent12549, scalar12549, tp12549, tm12549, ep12549, em12549, dsL]
  · norm_num [world12549, agent12549, scalar12549, tp12549, tm12549, ep12549, em12549, dsL]
  · norm_num [world12549, agent12549, scalar12549, tp12549, tm12549, ep12549, em12549, dsL]
  · norm_num [world12549, agent12549, scalar12549, tp12549, tm12549, ep12549, em12549, dsL]
  · norm_num [world12549, agent12549, scalar12549, tp12549, tm12549, ep12549, em12549, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12549, agent12549, tp12549, tm12549, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12549, agent12549, tp12549, tm12549, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12549, agent12549, scalar12549, tp12549, tm12549, ep12549, em12549, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12549, agent12549, tp12549, tm12549, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12549, agent12549, scalar12549, tp12549, tm12549, ep12549, em12549, dsL]

theorem tails12549 :
    exp (-((12549:ℝ)*ep12549)) ≤ scalar12549.upperTail ∧
    exp (-((12549:ℝ)*em12549)) ≤ scalar12549.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12549:ℝ)) (by norm_num [ep12549]) ?_)
      (show bp12549^8 ≤ scalar12549.upperTail by norm_num [bp12549, scalar12549])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12549, bp12549, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12549:ℝ)) (by norm_num [em12549]) ?_)
      (show bm12549^8 ≤ scalar12549.lowerTail by norm_num [bm12549, scalar12549])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12549, bm12549, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12549 :
    agent12549.root+dsL+scalar12549.worldRadius < √(1/100/aL) ∧
    2*(agent12549.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12549, agent12549, scalar12549, tp12549, tm12549, ep12549, em12549, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12549, agent12549, scalar12549, tp12549, tm12549, ep12549, em12549, dsL]

noncomputable def master12549 : MasterCertificate 12549 world12549 agent12549 :=
  master scalar12549 dsL tp12549 tm12549 ep12549 em12549
    (by norm_num [dsL]) (by norm_num [tp12549]) (by norm_num [tm12549])
    (by norm_num [ep12549]) (by norm_num [em12549])
    positive12549 negative12549 tails12549.1 tails12549.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12549.1 tailGuards12549.2

theorem preserves12549 : master12549.toScalarCertificate = scalar12549 := rfl

end BstLean.Part268
