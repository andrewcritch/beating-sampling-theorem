import BstLean.Part261Checker
import BstLean.Part268Scalar5
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12475 : ℝ := (2294725183 / 10000000000)
noncomputable def tm12475 : ℝ := (-((6014527099 / 10000000000)))
noncomputable def ep12475 : ℝ := (25386288426568419 / 50000000000000000000)
noncomputable def em12475 : ℝ := (49540803770688539 / 100000000000000000000)
noncomputable def bp12475 : ℝ := (45305811601513607681 / 100000000000000000000)
noncomputable def bm12475 : ℝ := (23092227675086501377 / 50000000000000000000)

theorem positive12475 :
    Eplus aL (agent12475.root+dsL) scalar12475.worldRadius world12475.frame
      agent12475.frame tp12475 ≤ -ep12475 := by
  apply positive_check (eT := (28880535692608938339 / 25000000000000000000)) (y := (4711304802052480989 / 12500000000000000000)) (u := (145776491729631781279 / 100000000000000000000))
  · norm_num [world12475, agent12475, scalar12475, tp12475, tm12475, ep12475, em12475, dsL]
  · norm_num [world12475, agent12475, scalar12475, tp12475, tm12475, ep12475, em12475, dsL]
  · norm_num [world12475, agent12475, scalar12475, tp12475, tm12475, ep12475, em12475, dsL]
  · norm_num [world12475, agent12475, scalar12475, tp12475, tm12475, ep12475, em12475, dsL]
  · norm_num [world12475, agent12475, scalar12475, tp12475, tm12475, ep12475, em12475, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12475, agent12475, tp12475, tm12475, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12475, agent12475, scalar12475, tp12475, tm12475, ep12475, em12475, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12475, agent12475, tp12475, tm12475, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12475, agent12475, scalar12475, tp12475, tm12475, ep12475, em12475, dsL]

theorem negative12475 :
    Eminus aL (agent12475.root+dsL) scalar12475.worldRadius world12475.frame
      agent12475.frame tm12475 ≤ -em12475 := by
  apply negative_check (lo := (17127461293492333043 / 25000000000000000000)) (hi := (68509845173969332173 / 100000000000000000000))
    (y := (-((71705087754414370179 / 100000000000000000000)))) (u := (4881898667716786971 / 10000000000000000000))
  · norm_num [world12475, agent12475, scalar12475, tp12475, tm12475, ep12475, em12475, dsL]
  · norm_num [world12475, agent12475, scalar12475, tp12475, tm12475, ep12475, em12475, dsL]
  · norm_num [world12475, agent12475, scalar12475, tp12475, tm12475, ep12475, em12475, dsL]
  · norm_num [world12475, agent12475, scalar12475, tp12475, tm12475, ep12475, em12475, dsL]
  · norm_num [world12475, agent12475, scalar12475, tp12475, tm12475, ep12475, em12475, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12475, agent12475, tp12475, tm12475, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12475, agent12475, tp12475, tm12475, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12475, agent12475, scalar12475, tp12475, tm12475, ep12475, em12475, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12475, agent12475, tp12475, tm12475, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12475, agent12475, scalar12475, tp12475, tm12475, ep12475, em12475, dsL]

theorem tails12475 :
    exp (-((12475:ℝ)*ep12475)) ≤ scalar12475.upperTail ∧
    exp (-((12475:ℝ)*em12475)) ≤ scalar12475.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12475:ℝ)) (by norm_num [ep12475]) ?_)
      (show bp12475^8 ≤ scalar12475.upperTail by norm_num [bp12475, scalar12475])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12475, bp12475, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12475:ℝ)) (by norm_num [em12475]) ?_)
      (show bm12475^8 ≤ scalar12475.lowerTail by norm_num [bm12475, scalar12475])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12475, bm12475, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12475 :
    agent12475.root+dsL+scalar12475.worldRadius < √(1/100/aL) ∧
    2*(agent12475.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12475, agent12475, scalar12475, tp12475, tm12475, ep12475, em12475, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12475, agent12475, scalar12475, tp12475, tm12475, ep12475, em12475, dsL]

noncomputable def master12475 : MasterCertificate 12475 world12475 agent12475 :=
  master scalar12475 dsL tp12475 tm12475 ep12475 em12475
    (by norm_num [dsL]) (by norm_num [tp12475]) (by norm_num [tm12475])
    (by norm_num [ep12475]) (by norm_num [em12475])
    positive12475 negative12475 tails12475.1 tails12475.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12475.1 tailGuards12475.2

theorem preserves12475 : master12475.toScalarCertificate = scalar12475 := rfl

noncomputable def tp12476 : ℝ := (1147409071 / 5000000000)
noncomputable def tm12476 : ℝ := (-((60147281 / 100000000)))
noncomputable def ep12476 : ℝ := (50775461034738123 / 100000000000000000000)
noncomputable def em12476 : ℝ := (49543294556646781 / 100000000000000000000)
noncomputable def bp12476 : ℝ := (45300898700319475393 / 100000000000000000000)
noncomputable def bm12476 : ℝ := (23089900792892916413 / 50000000000000000000)

theorem positive12476 :
    Eplus aL (agent12476.root+dsL) scalar12476.worldRadius world12476.frame
      agent12476.frame tp12476 ≤ -ep12476 := by
  apply positive_check (eT := (3610076169636989089 / 3125000000000000000)) (y := (18845655334637185763 / 50000000000000000000)) (u := (145777763274787653769 / 100000000000000000000))
  · norm_num [world12476, agent12476, scalar12476, tp12476, tm12476, ep12476, em12476, dsL]
  · norm_num [world12476, agent12476, scalar12476, tp12476, tm12476, ep12476, em12476, dsL]
  · norm_num [world12476, agent12476, scalar12476, tp12476, tm12476, ep12476, em12476, dsL]
  · norm_num [world12476, agent12476, scalar12476, tp12476, tm12476, ep12476, em12476, dsL]
  · norm_num [world12476, agent12476, scalar12476, tp12476, tm12476, ep12476, em12476, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12476, agent12476, tp12476, tm12476, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12476, agent12476, scalar12476, tp12476, tm12476, ep12476, em12476, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12476, agent12476, tp12476, tm12476, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12476, agent12476, scalar12476, tp12476, tm12476, ep12476, em12476, dsL]

theorem negative12476 :
    Eminus aL (agent12476.root+dsL) scalar12476.worldRadius world12476.frame
      agent12476.frame tm12476 ≤ -em12476 := by
  apply negative_check (lo := (3425478543810633189 / 5000000000000000000)) (hi := (68509570876212663781 / 100000000000000000000))
    (y := (-((71705248721869151763 / 100000000000000000000)))) (u := (48818908094550811549 / 100000000000000000000))
  · norm_num [world12476, agent12476, scalar12476, tp12476, tm12476, ep12476, em12476, dsL]
  · norm_num [world12476, agent12476, scalar12476, tp12476, tm12476, ep12476, em12476, dsL]
  · norm_num [world12476, agent12476, scalar12476, tp12476, tm12476, ep12476, em12476, dsL]
  · norm_num [world12476, agent12476, scalar12476, tp12476, tm12476, ep12476, em12476, dsL]
  · norm_num [world12476, agent12476, scalar12476, tp12476, tm12476, ep12476, em12476, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12476, agent12476, tp12476, tm12476, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12476, agent12476, tp12476, tm12476, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12476, agent12476, scalar12476, tp12476, tm12476, ep12476, em12476, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12476, agent12476, tp12476, tm12476, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12476, agent12476, scalar12476, tp12476, tm12476, ep12476, em12476, dsL]

theorem tails12476 :
    exp (-((12476:ℝ)*ep12476)) ≤ scalar12476.upperTail ∧
    exp (-((12476:ℝ)*em12476)) ≤ scalar12476.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12476:ℝ)) (by norm_num [ep12476]) ?_)
      (show bp12476^8 ≤ scalar12476.upperTail by norm_num [bp12476, scalar12476])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12476, bp12476, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12476:ℝ)) (by norm_num [em12476]) ?_)
      (show bm12476^8 ≤ scalar12476.lowerTail by norm_num [bm12476, scalar12476])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12476, bm12476, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12476 :
    agent12476.root+dsL+scalar12476.worldRadius < √(1/100/aL) ∧
    2*(agent12476.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12476, agent12476, scalar12476, tp12476, tm12476, ep12476, em12476, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12476, agent12476, scalar12476, tp12476, tm12476, ep12476, em12476, dsL]

noncomputable def master12476 : MasterCertificate 12476 world12476 agent12476 :=
  master scalar12476 dsL tp12476 tm12476 ep12476 em12476
    (by norm_num [dsL]) (by norm_num [tp12476]) (by norm_num [tm12476])
    (by norm_num [ep12476]) (by norm_num [em12476])
    positive12476 negative12476 tails12476.1 tails12476.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12476.1 tailGuards12476.2

theorem preserves12476 : master12476.toScalarCertificate = scalar12476 := rfl

noncomputable def tp12477 : ℝ := (2294911133 / 10000000000)
noncomputable def tm12477 : ℝ := (-((1202985819 / 2000000000)))
noncomputable def ep12477 : ℝ := (6347292942525299 / 12500000000000000000)
noncomputable def em12477 : ℝ := (3096611488313919 / 6250000000000000000)
noncomputable def bp12477 : ℝ := (45295987189371963831 / 100000000000000000000)
noncomputable def bm12477 : ℝ := (2885946819021605549 / 6250000000000000000)

theorem positive12477 :
    Eplus aL (agent12477.root+dsL) scalar12477.worldRadius world12477.frame
      agent12477.frame tp12477 ≤ -ep12477 := by
  apply positive_check (eT := (115522732351095327991 / 100000000000000000000)) (y := (18846091873892593503 / 50000000000000000000)) (u := (145779036034668441823 / 100000000000000000000))
  · norm_num [world12477, agent12477, scalar12477, tp12477, tm12477, ep12477, em12477, dsL]
  · norm_num [world12477, agent12477, scalar12477, tp12477, tm12477, ep12477, em12477, dsL]
  · norm_num [world12477, agent12477, scalar12477, tp12477, tm12477, ep12477, em12477, dsL]
  · norm_num [world12477, agent12477, scalar12477, tp12477, tm12477, ep12477, em12477, dsL]
  · norm_num [world12477, agent12477, scalar12477, tp12477, tm12477, ep12477, em12477, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12477, agent12477, tp12477, tm12477, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12477, agent12477, scalar12477, tp12477, tm12477, ep12477, em12477, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12477, agent12477, tp12477, tm12477, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12477, agent12477, scalar12477, tp12477, tm12477, ep12477, em12477, dsL]

theorem negative12477 :
    Eminus aL (agent12477.root+dsL) scalar12477.worldRadius world12477.frame
      agent12477.frame tm12477 ≤ -em12477 := by
  apply negative_check (lo := (2140915517123011649 / 3125000000000000000)) (hi := (68509296547936372769 / 100000000000000000000))
    (y := (-((35852704933075702837 / 50000000000000000000)))) (u := (9763765885147028711 / 20000000000000000000))
  · norm_num [world12477, agent12477, scalar12477, tp12477, tm12477, ep12477, em12477, dsL]
  · norm_num [world12477, agent12477, scalar12477, tp12477, tm12477, ep12477, em12477, dsL]
  · norm_num [world12477, agent12477, scalar12477, tp12477, tm12477, ep12477, em12477, dsL]
  · norm_num [world12477, agent12477, scalar12477, tp12477, tm12477, ep12477, em12477, dsL]
  · norm_num [world12477, agent12477, scalar12477, tp12477, tm12477, ep12477, em12477, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12477, agent12477, tp12477, tm12477, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12477, agent12477, tp12477, tm12477, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12477, agent12477, scalar12477, tp12477, tm12477, ep12477, em12477, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12477, agent12477, tp12477, tm12477, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12477, agent12477, scalar12477, tp12477, tm12477, ep12477, em12477, dsL]

theorem tails12477 :
    exp (-((12477:ℝ)*ep12477)) ≤ scalar12477.upperTail ∧
    exp (-((12477:ℝ)*em12477)) ≤ scalar12477.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12477:ℝ)) (by norm_num [ep12477]) ?_)
      (show bp12477^8 ≤ scalar12477.upperTail by norm_num [bp12477, scalar12477])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12477, bp12477, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12477:ℝ)) (by norm_num [em12477]) ?_)
      (show bm12477^8 ≤ scalar12477.lowerTail by norm_num [bm12477, scalar12477])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12477, bm12477, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12477 :
    agent12477.root+dsL+scalar12477.worldRadius < √(1/100/aL) ∧
    2*(agent12477.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12477, agent12477, scalar12477, tp12477, tm12477, ep12477, em12477, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12477, agent12477, scalar12477, tp12477, tm12477, ep12477, em12477, dsL]

noncomputable def master12477 : MasterCertificate 12477 world12477 agent12477 :=
  master scalar12477 dsL tp12477 tm12477 ep12477 em12477
    (by norm_num [dsL]) (by norm_num [tp12477]) (by norm_num [tm12477])
    (by norm_num [ep12477]) (by norm_num [em12477])
    positive12477 negative12477 tails12477.1 tails12477.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12477.1 tailGuards12477.2

theorem preserves12477 : master12477.toScalarCertificate = scalar12477 := rfl

noncomputable def tp12478 : ℝ := (2295003961 / 10000000000)
noncomputable def tm12478 : ℝ := (-((6015130033 / 10000000000)))
noncomputable def ep12478 : ℝ := (12695305906123479 / 25000000000000000000)
noncomputable def em12478 : ℝ := (49548270822855711 / 100000000000000000000)
noncomputable def bp12478 : ℝ := (4529107759493285707 / 10000000000000000000)
noncomputable def bm12478 : ℝ := (23085249211069620513 / 50000000000000000000)

theorem positive12478 :
    Eplus aL (agent12478.root+dsL) scalar12478.worldRadius world12478.frame
      agent12478.frame tp12478 ≤ -ep12478 := by
  apply positive_check (eT := (5776151306107029493 / 5000000000000000000)) (y := (301544437326896533 / 800000000000000000)) (u := (7289015282808712109 / 5000000000000000000))
  · norm_num [world12478, agent12478, scalar12478, tp12478, tm12478, ep12478, em12478, dsL]
  · norm_num [world12478, agent12478, scalar12478, tp12478, tm12478, ep12478, em12478, dsL]
  · norm_num [world12478, agent12478, scalar12478, tp12478, tm12478, ep12478, em12478, dsL]
  · norm_num [world12478, agent12478, scalar12478, tp12478, tm12478, ep12478, em12478, dsL]
  · norm_num [world12478, agent12478, scalar12478, tp12478, tm12478, ep12478, em12478, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12478, agent12478, tp12478, tm12478, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12478, agent12478, scalar12478, tp12478, tm12478, ep12478, em12478, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12478, agent12478, tp12478, tm12478, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12478, agent12478, scalar12478, tp12478, tm12478, ep12478, em12478, dsL]

theorem negative12478 :
    Eminus aL (agent12478.root+dsL) scalar12478.worldRadius world12478.frame
      agent12478.frame tm12478 ≤ -em12478 := by
  apply negative_check (lo := (6850902240885528779 / 10000000000000000000)) (hi := (68509022408855287791 / 100000000000000000000))
    (y := (-((8963196443475143013 / 12500000000000000000)))) (u := (9763750098942030709 / 20000000000000000000))
  · norm_num [world12478, agent12478, scalar12478, tp12478, tm12478, ep12478, em12478, dsL]
  · norm_num [world12478, agent12478, scalar12478, tp12478, tm12478, ep12478, em12478, dsL]
  · norm_num [world12478, agent12478, scalar12478, tp12478, tm12478, ep12478, em12478, dsL]
  · norm_num [world12478, agent12478, scalar12478, tp12478, tm12478, ep12478, em12478, dsL]
  · norm_num [world12478, agent12478, scalar12478, tp12478, tm12478, ep12478, em12478, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12478, agent12478, tp12478, tm12478, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12478, agent12478, tp12478, tm12478, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12478, agent12478, scalar12478, tp12478, tm12478, ep12478, em12478, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12478, agent12478, tp12478, tm12478, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12478, agent12478, scalar12478, tp12478, tm12478, ep12478, em12478, dsL]

theorem tails12478 :
    exp (-((12478:ℝ)*ep12478)) ≤ scalar12478.upperTail ∧
    exp (-((12478:ℝ)*em12478)) ≤ scalar12478.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12478:ℝ)) (by norm_num [ep12478]) ?_)
      (show bp12478^8 ≤ scalar12478.upperTail by norm_num [bp12478, scalar12478])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12478, bp12478, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12478:ℝ)) (by norm_num [em12478]) ?_)
      (show bm12478^8 ≤ scalar12478.lowerTail by norm_num [bm12478, scalar12478])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12478, bm12478, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12478 :
    agent12478.root+dsL+scalar12478.worldRadius < √(1/100/aL) ∧
    2*(agent12478.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12478, agent12478, scalar12478, tp12478, tm12478, ep12478, em12478, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12478, agent12478, scalar12478, tp12478, tm12478, ep12478, em12478, dsL]

noncomputable def master12478 : MasterCertificate 12478 world12478 agent12478 :=
  master scalar12478 dsL tp12478 tm12478 ep12478 em12478
    (by norm_num [dsL]) (by norm_num [tp12478]) (by norm_num [tm12478])
    (by norm_num [ep12478]) (by norm_num [em12478])
    positive12478 negative12478 tails12478.1 tails12478.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12478.1 tailGuards12478.2

theorem preserves12478 : master12478.toScalarCertificate = scalar12478 := rfl

noncomputable def tp12479 : ℝ := (2295096819 / 10000000000)
noncomputable def tm12479 : ℝ := (-((37595817 / 62500000)))
noncomputable def ep12479 : ℝ := (50784103145123181 / 100000000000000000000)
noncomputable def em12479 : ℝ := (24775378646141989 / 50000000000000000000)
noncomputable def bp12479 : ℝ := (22643084302372986983 / 50000000000000000000)
noncomputable def bm12479 : ℝ := (46165848310465679947 / 100000000000000000000)

theorem positive12479 :
    Eplus aL (agent12479.root+dsL) scalar12479.worldRadius world12479.frame
      agent12479.frame tp12479 ≤ -ep12479 := by
  apply positive_check (eT := (115523320143414556259 / 100000000000000000000)) (y := (37693926428876612531 / 100000000000000000000)) (u := (72890788260250449607 / 50000000000000000000))
  · norm_num [world12479, agent12479, scalar12479, tp12479, tm12479, ep12479, em12479, dsL]
  · norm_num [world12479, agent12479, scalar12479, tp12479, tm12479, ep12479, em12479, dsL]
  · norm_num [world12479, agent12479, scalar12479, tp12479, tm12479, ep12479, em12479, dsL]
  · norm_num [world12479, agent12479, scalar12479, tp12479, tm12479, ep12479, em12479, dsL]
  · norm_num [world12479, agent12479, scalar12479, tp12479, tm12479, ep12479, em12479, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12479, agent12479, tp12479, tm12479, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12479, agent12479, scalar12479, tp12479, tm12479, ep12479, em12479, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12479, agent12479, tp12479, tm12479, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12479, agent12479, scalar12479, tp12479, tm12479, ep12479, em12479, dsL]

theorem negative12479 :
    Eminus aL (agent12479.root+dsL) scalar12479.worldRadius world12479.frame
      agent12479.frame tm12479 ≤ -em12479 := by
  apply negative_check (lo := (68508749294622934829 / 100000000000000000000)) (hi := (6850874929462293483 / 10000000000000000000))
    (y := (-((71705731550378373231 / 100000000000000000000)))) (u := (12204668095878420233 / 25000000000000000000))
  · norm_num [world12479, agent12479, scalar12479, tp12479, tm12479, ep12479, em12479, dsL]
  · norm_num [world12479, agent12479, scalar12479, tp12479, tm12479, ep12479, em12479, dsL]
  · norm_num [world12479, agent12479, scalar12479, tp12479, tm12479, ep12479, em12479, dsL]
  · norm_num [world12479, agent12479, scalar12479, tp12479, tm12479, ep12479, em12479, dsL]
  · norm_num [world12479, agent12479, scalar12479, tp12479, tm12479, ep12479, em12479, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12479, agent12479, tp12479, tm12479, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12479, agent12479, tp12479, tm12479, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12479, agent12479, scalar12479, tp12479, tm12479, ep12479, em12479, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12479, agent12479, tp12479, tm12479, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12479, agent12479, scalar12479, tp12479, tm12479, ep12479, em12479, dsL]

theorem tails12479 :
    exp (-((12479:ℝ)*ep12479)) ≤ scalar12479.upperTail ∧
    exp (-((12479:ℝ)*em12479)) ≤ scalar12479.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12479:ℝ)) (by norm_num [ep12479]) ?_)
      (show bp12479^8 ≤ scalar12479.upperTail by norm_num [bp12479, scalar12479])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12479, bp12479, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12479:ℝ)) (by norm_num [em12479]) ?_)
      (show bm12479^8 ≤ scalar12479.lowerTail by norm_num [bm12479, scalar12479])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12479, bm12479, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12479 :
    agent12479.root+dsL+scalar12479.worldRadius < √(1/100/aL) ∧
    2*(agent12479.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12479, agent12479, scalar12479, tp12479, tm12479, ep12479, em12479, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12479, agent12479, scalar12479, tp12479, tm12479, ep12479, em12479, dsL]

noncomputable def master12479 : MasterCertificate 12479 world12479 agent12479 :=
  master scalar12479 dsL tp12479 tm12479 ep12479 em12479
    (by norm_num [dsL]) (by norm_num [tp12479]) (by norm_num [tm12479])
    (by norm_num [ep12479]) (by norm_num [em12479])
    positive12479 negative12479 tails12479.1 tails12479.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12479.1 tailGuards12479.2

theorem preserves12479 : master12479.toScalarCertificate = scalar12479 := rfl

noncomputable def tp12480 : ℝ := (1147632973 / 5000000000)
noncomputable def tm12480 : ℝ := (-((93996281 / 156250000)))
noncomputable def ep12480 : ℝ := (25394225062437139 / 50000000000000000000)
noncomputable def em12480 : ℝ := (49554840279008109 / 100000000000000000000)
noncomputable def bp12480 : ℝ := (45280223237521562439 / 100000000000000000000)
noncomputable def bm12480 : ℝ := (46160048718938579483 / 100000000000000000000)

theorem positive12480 :
    Eplus aL (agent12480.root+dsL) scalar12480.worldRadius world12480.frame
      agent12480.frame tp12480 ≤ -ep12480 := by
  apply positive_check (eT := (56408285235142903 / 48828125000000000)) (y := (18847032644040655089 / 50000000000000000000)) (u := (145781778951779198473 / 100000000000000000000))
  · norm_num [world12480, agent12480, scalar12480, tp12480, tm12480, ep12480, em12480, dsL]
  · norm_num [world12480, agent12480, scalar12480, tp12480, tm12480, ep12480, em12480, dsL]
  · norm_num [world12480, agent12480, scalar12480, tp12480, tm12480, ep12480, em12480, dsL]
  · norm_num [world12480, agent12480, scalar12480, tp12480, tm12480, ep12480, em12480, dsL]
  · norm_num [world12480, agent12480, scalar12480, tp12480, tm12480, ep12480, em12480, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12480, agent12480, tp12480, tm12480, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12480, agent12480, scalar12480, tp12480, tm12480, ep12480, em12480, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12480, agent12480, tp12480, tm12480, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12480, agent12480, scalar12480, tp12480, tm12480, ep12480, em12480, dsL]

theorem negative12480 :
    Eminus aL (agent12480.root+dsL) scalar12480.worldRadius world12480.frame
      agent12480.frame tm12480 ≤ -em12480 := by
  apply negative_check (lo := (17126870740976806627 / 25000000000000000000)) (hi := (68507482963907226509 / 100000000000000000000))
    (y := (-((71703958813042560953 / 100000000000000000000)))) (u := (48819537818016788969 / 100000000000000000000))
  · norm_num [world12480, agent12480, scalar12480, tp12480, tm12480, ep12480, em12480, dsL]
  · norm_num [world12480, agent12480, scalar12480, tp12480, tm12480, ep12480, em12480, dsL]
  · norm_num [world12480, agent12480, scalar12480, tp12480, tm12480, ep12480, em12480, dsL]
  · norm_num [world12480, agent12480, scalar12480, tp12480, tm12480, ep12480, em12480, dsL]
  · norm_num [world12480, agent12480, scalar12480, tp12480, tm12480, ep12480, em12480, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12480, agent12480, tp12480, tm12480, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12480, agent12480, tp12480, tm12480, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12480, agent12480, scalar12480, tp12480, tm12480, ep12480, em12480, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12480, agent12480, tp12480, tm12480, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12480, agent12480, scalar12480, tp12480, tm12480, ep12480, em12480, dsL]

theorem tails12480 :
    exp (-((12480:ℝ)*ep12480)) ≤ scalar12480.upperTail ∧
    exp (-((12480:ℝ)*em12480)) ≤ scalar12480.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12480:ℝ)) (by norm_num [ep12480]) ?_)
      (show bp12480^8 ≤ scalar12480.upperTail by norm_num [bp12480, scalar12480])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12480, bp12480, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12480:ℝ)) (by norm_num [em12480]) ?_)
      (show bm12480^8 ≤ scalar12480.lowerTail by norm_num [bm12480, scalar12480])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12480, bm12480, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12480 :
    agent12480.root+dsL+scalar12480.worldRadius < √(1/100/aL) ∧
    2*(agent12480.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12480, agent12480, scalar12480, tp12480, tm12480, ep12480, em12480, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12480, agent12480, scalar12480, tp12480, tm12480, ep12480, em12480, dsL]

noncomputable def master12480 : MasterCertificate 12480 world12480 agent12480 :=
  master scalar12480 dsL tp12480 tm12480 ep12480 em12480
    (by norm_num [dsL]) (by norm_num [tp12480]) (by norm_num [tm12480])
    (by norm_num [ep12480]) (by norm_num [em12480])
    positive12480 negative12480 tails12480.1 tails12480.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12480.1 tailGuards12480.2

theorem preserves12480 : master12480.toScalarCertificate = scalar12480 := rfl

noncomputable def tp12481 : ℝ := (71729959 / 312500000)
noncomputable def tm12481 : ℝ := (-((6015962457 / 10000000000)))
noncomputable def ep12481 : ℝ := (25395663157885969 / 50000000000000000000)
noncomputable def em12481 : ℝ := (49557323647750819 / 100000000000000000000)
noncomputable def bp12481 : ℝ := (22637658520433780081 / 50000000000000000000)
noncomputable def bm12481 : ℝ := (46155401226536020891 / 100000000000000000000)

theorem positive12481 :
    Eplus aL (agent12481.root+dsL) scalar12481.worldRadius world12481.frame
      agent12481.frame tp12481 ≤ -ep12481 := by
  apply positive_check (eT := (115524461393747452127 / 100000000000000000000)) (y := (9423733997496039523 / 25000000000000000000)) (u := (36445762070507142613 / 25000000000000000000))
  · norm_num [world12481, agent12481, scalar12481, tp12481, tm12481, ep12481, em12481, dsL]
  · norm_num [world12481, agent12481, scalar12481, tp12481, tm12481, ep12481, em12481, dsL]
  · norm_num [world12481, agent12481, scalar12481, tp12481, tm12481, ep12481, em12481, dsL]
  · norm_num [world12481, agent12481, scalar12481, tp12481, tm12481, ep12481, em12481, dsL]
  · norm_num [world12481, agent12481, scalar12481, tp12481, tm12481, ep12481, em12481, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12481, agent12481, tp12481, tm12481, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12481, agent12481, scalar12481, tp12481, tm12481, ep12481, em12481, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12481, agent12481, tp12481, tm12481, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12481, agent12481, scalar12481, tp12481, tm12481, ep12481, em12481, dsL]

theorem negative12481 :
    Eminus aL (agent12481.root+dsL) scalar12481.worldRadius world12481.frame
      agent12481.frame tm12481 ≤ -em12481 := by
  apply negative_check (lo := (34253605342623782689 / 50000000000000000000)) (hi := (68507210685247565379 / 100000000000000000000))
    (y := (-((71704118336860979239 / 100000000000000000000)))) (u := (48819459939288045087 / 100000000000000000000))
  · norm_num [world12481, agent12481, scalar12481, tp12481, tm12481, ep12481, em12481, dsL]
  · norm_num [world12481, agent12481, scalar12481, tp12481, tm12481, ep12481, em12481, dsL]
  · norm_num [world12481, agent12481, scalar12481, tp12481, tm12481, ep12481, em12481, dsL]
  · norm_num [world12481, agent12481, scalar12481, tp12481, tm12481, ep12481, em12481, dsL]
  · norm_num [world12481, agent12481, scalar12481, tp12481, tm12481, ep12481, em12481, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12481, agent12481, tp12481, tm12481, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12481, agent12481, tp12481, tm12481, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12481, agent12481, scalar12481, tp12481, tm12481, ep12481, em12481, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12481, agent12481, tp12481, tm12481, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12481, agent12481, scalar12481, tp12481, tm12481, ep12481, em12481, dsL]

theorem tails12481 :
    exp (-((12481:ℝ)*ep12481)) ≤ scalar12481.upperTail ∧
    exp (-((12481:ℝ)*em12481)) ≤ scalar12481.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12481:ℝ)) (by norm_num [ep12481]) ?_)
      (show bp12481^8 ≤ scalar12481.upperTail by norm_num [bp12481, scalar12481])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12481, bp12481, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12481:ℝ)) (by norm_num [em12481]) ?_)
      (show bm12481^8 ≤ scalar12481.lowerTail by norm_num [bm12481, scalar12481])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12481, bm12481, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12481 :
    agent12481.root+dsL+scalar12481.worldRadius < √(1/100/aL) ∧
    2*(agent12481.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12481, agent12481, scalar12481, tp12481, tm12481, ep12481, em12481, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12481, agent12481, scalar12481, tp12481, tm12481, ep12481, em12481, dsL]

noncomputable def master12481 : MasterCertificate 12481 world12481 agent12481 :=
  master scalar12481 dsL tp12481 tm12481 ep12481 em12481
    (by norm_num [dsL]) (by norm_num [tp12481]) (by norm_num [tm12481])
    (by norm_num [ep12481]) (by norm_num [em12481])
    positive12481 negative12481 tails12481.1 tails12481.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12481.1 tailGuards12481.2

theorem preserves12481 : master12481.toScalarCertificate = scalar12481 := rfl

noncomputable def tp12482 : ℝ := (1147725689 / 5000000000)
noncomputable def tm12482 : ℝ := (-((6016162907 / 10000000000)))
noncomputable def ep12482 : ℝ := (12698550209675141 / 25000000000000000000)
noncomputable def em12482 : ℝ := (24779902750202247 / 50000000000000000000)
noncomputable def bp12482 : ℝ := (9054082445686497659 / 20000000000000000000)
noncomputable def bm12482 : ℝ := (46150755007215489509 / 100000000000000000000)

theorem positive12482 :
    Eplus aL (agent12482.root+dsL) scalar12482.worldRadius world12482.frame
      agent12482.frame tp12482 ≤ -ep12482 := by
  apply positive_check (eT := (14440594285071101841 / 12500000000000000000)) (y := (18847903068398769057 / 50000000000000000000)) (u := (72892158407048341231 / 50000000000000000000))
  · norm_num [world12482, agent12482, scalar12482, tp12482, tm12482, ep12482, em12482, dsL]
  · norm_num [world12482, agent12482, scalar12482, tp12482, tm12482, ep12482, em12482, dsL]
  · norm_num [world12482, agent12482, scalar12482, tp12482, tm12482, ep12482, em12482, dsL]
  · norm_num [world12482, agent12482, scalar12482, tp12482, tm12482, ep12482, em12482, dsL]
  · norm_num [world12482, agent12482, scalar12482, tp12482, tm12482, ep12482, em12482, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12482, agent12482, tp12482, tm12482, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12482, agent12482, scalar12482, tp12482, tm12482, ep12482, em12482, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12482, agent12482, tp12482, tm12482, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12482, agent12482, scalar12482, tp12482, tm12482, ep12482, em12482, dsL]

theorem negative12482 :
    Eminus aL (agent12482.root+dsL) scalar12482.worldRadius world12482.frame
      agent12482.frame tm12482 ≤ -em12482 := by
  apply negative_check (lo := (17126734612319619259 / 25000000000000000000)) (hi := (68506938449278477037 / 100000000000000000000))
    (y := (-((71704278281866063287 / 100000000000000000000)))) (u := (24409690927531404557 / 50000000000000000000))
  · norm_num [world12482, agent12482, scalar12482, tp12482, tm12482, ep12482, em12482, dsL]
  · norm_num [world12482, agent12482, scalar12482, tp12482, tm12482, ep12482, em12482, dsL]
  · norm_num [world12482, agent12482, scalar12482, tp12482, tm12482, ep12482, em12482, dsL]
  · norm_num [world12482, agent12482, scalar12482, tp12482, tm12482, ep12482, em12482, dsL]
  · norm_num [world12482, agent12482, scalar12482, tp12482, tm12482, ep12482, em12482, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12482, agent12482, tp12482, tm12482, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12482, agent12482, tp12482, tm12482, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12482, agent12482, scalar12482, tp12482, tm12482, ep12482, em12482, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12482, agent12482, tp12482, tm12482, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12482, agent12482, scalar12482, tp12482, tm12482, ep12482, em12482, dsL]

theorem tails12482 :
    exp (-((12482:ℝ)*ep12482)) ≤ scalar12482.upperTail ∧
    exp (-((12482:ℝ)*em12482)) ≤ scalar12482.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12482:ℝ)) (by norm_num [ep12482]) ?_)
      (show bp12482^8 ≤ scalar12482.upperTail by norm_num [bp12482, scalar12482])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12482, bp12482, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12482:ℝ)) (by norm_num [em12482]) ?_)
      (show bm12482^8 ≤ scalar12482.lowerTail by norm_num [bm12482, scalar12482])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12482, bm12482, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12482 :
    agent12482.root+dsL+scalar12482.worldRadius < √(1/100/aL) ∧
    2*(agent12482.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12482, agent12482, scalar12482, tp12482, tm12482, ep12482, em12482, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12482, agent12482, scalar12482, tp12482, tm12482, ep12482, em12482, dsL]

noncomputable def master12482 : MasterCertificate 12482 world12482 agent12482 :=
  master scalar12482 dsL tp12482 tm12482 ep12482 em12482
    (by norm_num [dsL]) (by norm_num [tp12482]) (by norm_num [tm12482])
    (by norm_num [ep12482]) (by norm_num [em12482])
    positive12482 negative12482 tails12482.1 tails12482.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12482.1 tailGuards12482.2

theorem preserves12482 : master12482.toScalarCertificate = scalar12482 := rfl

noncomputable def tp12483 : ℝ := (45910881 / 200000000)
noncomputable def tm12483 : ℝ := (-((6016363177 / 10000000000)))
noncomputable def ep12483 : ℝ := (25398537333476207 / 50000000000000000000)
noncomputable def em12483 : ℝ := (49562286674023711 / 100000000000000000000)
noncomputable def bp12483 : ℝ := (45265508112717088619 / 100000000000000000000)
noncomputable def bm12483 : ℝ := (4614610945822595217 / 10000000000000000000)

theorem positive12483 :
    Eplus aL (agent12483.root+dsL) scalar12483.worldRadius world12483.frame
      agent12483.frame tp12483 ≤ -ep12483 := by
  apply positive_check (eT := (57762523534502629691 / 50000000000000000000)) (y := (18848338216278916447 / 50000000000000000000)) (u := (145785585574346065577 / 100000000000000000000))
  · norm_num [world12483, agent12483, scalar12483, tp12483, tm12483, ep12483, em12483, dsL]
  · norm_num [world12483, agent12483, scalar12483, tp12483, tm12483, ep12483, em12483, dsL]
  · norm_num [world12483, agent12483, scalar12483, tp12483, tm12483, ep12483, em12483, dsL]
  · norm_num [world12483, agent12483, scalar12483, tp12483, tm12483, ep12483, em12483, dsL]
  · norm_num [world12483, agent12483, scalar12483, tp12483, tm12483, ep12483, em12483, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12483, agent12483, tp12483, tm12483, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12483, agent12483, scalar12483, tp12483, tm12483, ep12483, em12483, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12483, agent12483, tp12483, tm12483, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12483, agent12483, scalar12483, tp12483, tm12483, ep12483, em12483, dsL]

theorem negative12483 :
    Eminus aL (agent12483.root+dsL) scalar12483.worldRadius world12483.frame
      agent12483.frame tm12483 ≤ -em12483 := by
  apply negative_check (lo := (68506666932166993959 / 100000000000000000000)) (hi := (1712666673304174849 / 2500000000000000000))
    (y := (-((71704437530937023247 / 100000000000000000000)))) (u := (390554432885701281 / 800000000000000000))
  · norm_num [world12483, agent12483, scalar12483, tp12483, tm12483, ep12483, em12483, dsL]
  · norm_num [world12483, agent12483, scalar12483, tp12483, tm12483, ep12483, em12483, dsL]
  · norm_num [world12483, agent12483, scalar12483, tp12483, tm12483, ep12483, em12483, dsL]
  · norm_num [world12483, agent12483, scalar12483, tp12483, tm12483, ep12483, em12483, dsL]
  · norm_num [world12483, agent12483, scalar12483, tp12483, tm12483, ep12483, em12483, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12483, agent12483, tp12483, tm12483, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12483, agent12483, tp12483, tm12483, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12483, agent12483, scalar12483, tp12483, tm12483, ep12483, em12483, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12483, agent12483, tp12483, tm12483, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12483, agent12483, scalar12483, tp12483, tm12483, ep12483, em12483, dsL]

theorem tails12483 :
    exp (-((12483:ℝ)*ep12483)) ≤ scalar12483.upperTail ∧
    exp (-((12483:ℝ)*em12483)) ≤ scalar12483.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12483:ℝ)) (by norm_num [ep12483]) ?_)
      (show bp12483^8 ≤ scalar12483.upperTail by norm_num [bp12483, scalar12483])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12483, bp12483, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12483:ℝ)) (by norm_num [em12483]) ?_)
      (show bm12483^8 ≤ scalar12483.lowerTail by norm_num [bm12483, scalar12483])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12483, bm12483, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12483 :
    agent12483.root+dsL+scalar12483.worldRadius < √(1/100/aL) ∧
    2*(agent12483.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12483, agent12483, scalar12483, tp12483, tm12483, ep12483, em12483, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12483, agent12483, scalar12483, tp12483, tm12483, ep12483, em12483, dsL]

noncomputable def master12483 : MasterCertificate 12483 world12483 agent12483 :=
  master scalar12483 dsL tp12483 tm12483 ep12483 em12483
    (by norm_num [dsL]) (by norm_num [tp12483]) (by norm_num [tm12483])
    (by norm_num [ep12483]) (by norm_num [em12483])
    positive12483 negative12483 tails12483.1 tails12483.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12483.1 tailGuards12483.2

theorem preserves12483 : master12483.toScalarCertificate = scalar12483 := rfl

noncomputable def tp12484 : ℝ := (1147818339 / 5000000000)
noncomputable def tm12484 : ℝ := (-((240662541 / 400000000)))
noncomputable def ep12484 : ℝ := (12699986670830507 / 25000000000000000000)
noncomputable def em12484 : ℝ := (49564766175530111 / 100000000000000000000)
noncomputable def bp12484 : ℝ := (45260605482800952447 / 100000000000000000000)
noncomputable def bm12484 : ℝ := (23070732647315175939 / 50000000000000000000)

theorem positive12484 :
    Eplus aL (agent12484.root+dsL) scalar12484.worldRadius world12484.frame
      agent12484.frame tp12484 ≤ -ep12484 := by
  apply positive_check (eT := (57762669785120807019 / 50000000000000000000)) (y := (7539509272706371939 / 20000000000000000000)) (u := (72893426906913519599 / 50000000000000000000))
  · norm_num [world12484, agent12484, scalar12484, tp12484, tm12484, ep12484, em12484, dsL]
  · norm_num [world12484, agent12484, scalar12484, tp12484, tm12484, ep12484, em12484, dsL]
  · norm_num [world12484, agent12484, scalar12484, tp12484, tm12484, ep12484, em12484, dsL]
  · norm_num [world12484, agent12484, scalar12484, tp12484, tm12484, ep12484, em12484, dsL]
  · norm_num [world12484, agent12484, scalar12484, tp12484, tm12484, ep12484, em12484, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12484, agent12484, tp12484, tm12484, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12484, agent12484, scalar12484, tp12484, tm12484, ep12484, em12484, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12484, agent12484, tp12484, tm12484, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12484, agent12484, scalar12484, tp12484, tm12484, ep12484, em12484, dsL]

theorem negative12484 :
    Eminus aL (agent12484.root+dsL) scalar12484.worldRadius world12484.frame
      agent12484.frame tm12484 ≤ -em12484 := by
  apply negative_check (lo := (17126598755672563331 / 25000000000000000000)) (hi := (2740255800907610133 / 4000000000000000000))
    (y := (-((35852299032775276021 / 50000000000000000000)))) (u := (4881922573889438551 / 10000000000000000000))
  · norm_num [world12484, agent12484, scalar12484, tp12484, tm12484, ep12484, em12484, dsL]
  · norm_num [world12484, agent12484, scalar12484, tp12484, tm12484, ep12484, em12484, dsL]
  · norm_num [world12484, agent12484, scalar12484, tp12484, tm12484, ep12484, em12484, dsL]
  · norm_num [world12484, agent12484, scalar12484, tp12484, tm12484, ep12484, em12484, dsL]
  · norm_num [world12484, agent12484, scalar12484, tp12484, tm12484, ep12484, em12484, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12484, agent12484, tp12484, tm12484, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12484, agent12484, tp12484, tm12484, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12484, agent12484, scalar12484, tp12484, tm12484, ep12484, em12484, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12484, agent12484, tp12484, tm12484, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12484, agent12484, scalar12484, tp12484, tm12484, ep12484, em12484, dsL]

theorem tails12484 :
    exp (-((12484:ℝ)*ep12484)) ≤ scalar12484.upperTail ∧
    exp (-((12484:ℝ)*em12484)) ≤ scalar12484.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12484:ℝ)) (by norm_num [ep12484]) ?_)
      (show bp12484^8 ≤ scalar12484.upperTail by norm_num [bp12484, scalar12484])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12484, bp12484, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12484:ℝ)) (by norm_num [em12484]) ?_)
      (show bm12484^8 ≤ scalar12484.lowerTail by norm_num [bm12484, scalar12484])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12484, bm12484, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12484 :
    agent12484.root+dsL+scalar12484.worldRadius < √(1/100/aL) ∧
    2*(agent12484.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12484, agent12484, scalar12484, tp12484, tm12484, ep12484, em12484, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12484, agent12484, scalar12484, tp12484, tm12484, ep12484, em12484, dsL]

noncomputable def master12484 : MasterCertificate 12484 world12484 agent12484 :=
  master scalar12484 dsL tp12484 tm12484 ep12484 em12484
    (by norm_num [dsL]) (by norm_num [tp12484]) (by norm_num [tm12484])
    (by norm_num [ep12484]) (by norm_num [em12484])
    positive12484 negative12484 tails12484.1 tails12484.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12484.1 tailGuards12484.2

theorem preserves12484 : master12484.toScalarCertificate = scalar12484 := rfl

noncomputable def tp12485 : ℝ := (143483077 / 625000000)
noncomputable def tm12485 : ℝ := (-((6016763619 / 10000000000)))
noncomputable def ep12485 : ℝ := (50802816891233453 / 100000000000000000000)
noncomputable def em12485 : ℝ := (49567244014171577 / 100000000000000000000)
noncomputable def bp12485 : ℝ := (22627852168102779841 / 50000000000000000000)
noncomputable def bm12485 : ℝ := (230684112548675669 / 500000000000000000)

theorem positive12485 :
    Eplus aL (agent12485.root+dsL) scalar12485.worldRadius world12485.frame
      agent12485.frame tp12485 ≤ -ep12485 := by
  apply positive_check (eT := (115525631566374652683 / 100000000000000000000)) (y := (18849207751149674137 / 50000000000000000000)) (u := (36447030227349459627 / 25000000000000000000))
  · norm_num [world12485, agent12485, scalar12485, tp12485, tm12485, ep12485, em12485, dsL]
  · norm_num [world12485, agent12485, scalar12485, tp12485, tm12485, ep12485, em12485, dsL]
  · norm_num [world12485, agent12485, scalar12485, tp12485, tm12485, ep12485, em12485, dsL]
  · norm_num [world12485, agent12485, scalar12485, tp12485, tm12485, ep12485, em12485, dsL]
  · norm_num [world12485, agent12485, scalar12485, tp12485, tm12485, ep12485, em12485, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12485, agent12485, tp12485, tm12485, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12485, agent12485, scalar12485, tp12485, tm12485, ep12485, em12485, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12485, agent12485, tp12485, tm12485, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12485, agent12485, scalar12485, tp12485, tm12485, ep12485, em12485, dsL]

theorem negative12485 :
    Eminus aL (agent12485.root+dsL) scalar12485.worldRadius world12485.frame
      agent12485.frame tm12485 ≤ -em12485 := by
  apply negative_check (lo := (13701224830152879171 / 20000000000000000000)) (hi := (4281632759422774741 / 6250000000000000000))
    (y := (-((35852378521501174769 / 50000000000000000000)))) (u := (48819148127395010957 / 100000000000000000000))
  · norm_num [world12485, agent12485, scalar12485, tp12485, tm12485, ep12485, em12485, dsL]
  · norm_num [world12485, agent12485, scalar12485, tp12485, tm12485, ep12485, em12485, dsL]
  · norm_num [world12485, agent12485, scalar12485, tp12485, tm12485, ep12485, em12485, dsL]
  · norm_num [world12485, agent12485, scalar12485, tp12485, tm12485, ep12485, em12485, dsL]
  · norm_num [world12485, agent12485, scalar12485, tp12485, tm12485, ep12485, em12485, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12485, agent12485, tp12485, tm12485, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12485, agent12485, tp12485, tm12485, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12485, agent12485, scalar12485, tp12485, tm12485, ep12485, em12485, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12485, agent12485, tp12485, tm12485, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12485, agent12485, scalar12485, tp12485, tm12485, ep12485, em12485, dsL]

theorem tails12485 :
    exp (-((12485:ℝ)*ep12485)) ≤ scalar12485.upperTail ∧
    exp (-((12485:ℝ)*em12485)) ≤ scalar12485.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12485:ℝ)) (by norm_num [ep12485]) ?_)
      (show bp12485^8 ≤ scalar12485.upperTail by norm_num [bp12485, scalar12485])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12485, bp12485, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12485:ℝ)) (by norm_num [em12485]) ?_)
      (show bm12485^8 ≤ scalar12485.lowerTail by norm_num [bm12485, scalar12485])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12485, bm12485, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12485 :
    agent12485.root+dsL+scalar12485.worldRadius < √(1/100/aL) ∧
    2*(agent12485.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12485, agent12485, scalar12485, tp12485, tm12485, ep12485, em12485, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12485, agent12485, scalar12485, tp12485, tm12485, ep12485, em12485, dsL]

noncomputable def master12485 : MasterCertificate 12485 world12485 agent12485 :=
  master scalar12485 dsL tp12485 tm12485 ep12485 em12485
    (by norm_num [dsL]) (by norm_num [tp12485]) (by norm_num [tm12485])
    (by norm_num [ep12485]) (by norm_num [em12485])
    positive12485 negative12485 tails12485.1 tails12485.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12485.1 tailGuards12485.2

theorem preserves12485 : master12485.toScalarCertificate = scalar12485 := rfl

noncomputable def tp12486 : ℝ := (2295821759 / 10000000000)
noncomputable def tm12486 : ℝ := (-((752120477 / 1250000000)))
noncomputable def ep12486 : ℝ := (50805686872116867 / 100000000000000000000)
noncomputable def em12486 : ℝ := (24784860803206339 / 50000000000000000000)
noncomputable def bp12486 : ℝ := (45250803555982795451 / 100000000000000000000)
noncomputable def bm12486 : ℝ := (23066090041820002303 / 50000000000000000000)

theorem positive12486 :
    Eplus aL (agent12486.root+dsL) scalar12486.worldRadius world12486.frame
      agent12486.frame tp12486 ≤ -ep12486 := by
  apply positive_check (eT := (28881480849701427591 / 25000000000000000000)) (y := (18849642290964493647 / 50000000000000000000)) (u := (145789387929764795571 / 100000000000000000000))
  · norm_num [world12486, agent12486, scalar12486, tp12486, tm12486, ep12486, em12486, dsL]
  · norm_num [world12486, agent12486, scalar12486, tp12486, tm12486, ep12486, em12486, dsL]
  · norm_num [world12486, agent12486, scalar12486, tp12486, tm12486, ep12486, em12486, dsL]
  · norm_num [world12486, agent12486, scalar12486, tp12486, tm12486, ep12486, em12486, dsL]
  · norm_num [world12486, agent12486, scalar12486, tp12486, tm12486, ep12486, em12486, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12486, agent12486, tp12486, tm12486, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12486, agent12486, scalar12486, tp12486, tm12486, ep12486, em12486, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12486, agent12486, tp12486, tm12486, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12486, agent12486, scalar12486, tp12486, tm12486, ep12486, em12486, dsL]

theorem negative12486 :
    Eminus aL (agent12486.root+dsL) scalar12486.worldRadius world12486.frame
      agent12486.frame tm12486 ≤ -em12486 := by
  apply negative_check (lo := (34252926389404981977 / 50000000000000000000)) (hi := (13701170555761992791 / 20000000000000000000))
    (y := (-((8963114778310408561 / 12500000000000000000)))) (u := (24409534719528060281 / 50000000000000000000))
  · norm_num [world12486, agent12486, scalar12486, tp12486, tm12486, ep12486, em12486, dsL]
  · norm_num [world12486, agent12486, scalar12486, tp12486, tm12486, ep12486, em12486, dsL]
  · norm_num [world12486, agent12486, scalar12486, tp12486, tm12486, ep12486, em12486, dsL]
  · norm_num [world12486, agent12486, scalar12486, tp12486, tm12486, ep12486, em12486, dsL]
  · norm_num [world12486, agent12486, scalar12486, tp12486, tm12486, ep12486, em12486, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12486, agent12486, tp12486, tm12486, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12486, agent12486, tp12486, tm12486, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12486, agent12486, scalar12486, tp12486, tm12486, ep12486, em12486, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12486, agent12486, tp12486, tm12486, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12486, agent12486, scalar12486, tp12486, tm12486, ep12486, em12486, dsL]

theorem tails12486 :
    exp (-((12486:ℝ)*ep12486)) ≤ scalar12486.upperTail ∧
    exp (-((12486:ℝ)*em12486)) ≤ scalar12486.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12486:ℝ)) (by norm_num [ep12486]) ?_)
      (show bp12486^8 ≤ scalar12486.upperTail by norm_num [bp12486, scalar12486])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12486, bp12486, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12486:ℝ)) (by norm_num [em12486]) ?_)
      (show bm12486^8 ≤ scalar12486.lowerTail by norm_num [bm12486, scalar12486])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12486, bm12486, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12486 :
    agent12486.root+dsL+scalar12486.worldRadius < √(1/100/aL) ∧
    2*(agent12486.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12486, agent12486, scalar12486, tp12486, tm12486, ep12486, em12486, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12486, agent12486, scalar12486, tp12486, tm12486, ep12486, em12486, dsL]

noncomputable def master12486 : MasterCertificate 12486 world12486 agent12486 :=
  master scalar12486 dsL tp12486 tm12486 ep12486 em12486
    (by norm_num [dsL]) (by norm_num [tp12486]) (by norm_num [tm12486])
    (by norm_num [ep12486]) (by norm_num [em12486])
    positive12486 negative12486 tails12486.1 tails12486.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12486.1 tailGuards12486.2

theorem preserves12486 : master12486.toScalarCertificate = scalar12486 := rfl

noncomputable def tp12487 : ℝ := (1147957143 / 5000000000)
noncomputable def tm12487 : ℝ := (-((3008581803 / 5000000000)))
noncomputable def ep12487 : ℝ := (25404277127614009 / 50000000000000000000)
noncomputable def em12487 : ℝ := (12393049205657203 / 25000000000000000000)
noncomputable def bp12487 : ℝ := (45245904816462567809 / 100000000000000000000)
noncomputable def bm12487 : ℝ := (46127539549688567447 / 100000000000000000000)

theorem positive12487 :
    Eplus aL (agent12487.root+dsL) scalar12487.worldRadius world12487.frame
      agent12487.frame tp12487 ≤ -ep12487 := by
  apply positive_check (eT := (14440776907947894409 / 12500000000000000000)) (y := (37700154119791345559 / 100000000000000000000)) (u := (1822383195365046257 / 1250000000000000000))
  · norm_num [world12487, agent12487, scalar12487, tp12487, tm12487, ep12487, em12487, dsL]
  · norm_num [world12487, agent12487, scalar12487, tp12487, tm12487, ep12487, em12487, dsL]
  · norm_num [world12487, agent12487, scalar12487, tp12487, tm12487, ep12487, em12487, dsL]
  · norm_num [world12487, agent12487, scalar12487, tp12487, tm12487, ep12487, em12487, dsL]
  · norm_num [world12487, agent12487, scalar12487, tp12487, tm12487, ep12487, em12487, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12487, agent12487, tp12487, tm12487, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12487, agent12487, scalar12487, tp12487, tm12487, ep12487, em12487, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12487, agent12487, tp12487, tm12487, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12487, agent12487, scalar12487, tp12487, tm12487, ep12487, em12487, dsL]

theorem negative12487 :
    Eminus aL (agent12487.root+dsL) scalar12487.worldRadius world12487.frame
      agent12487.frame tm12487 ≤ -em12487 := by
  apply negative_check (lo := (68505583103222180351 / 100000000000000000000)) (hi := (133799966998480821 / 195312500000000000))
    (y := (-((4481567237942029251 / 6250000000000000000)))) (u := (24409496254869734811 / 50000000000000000000))
  · norm_num [world12487, agent12487, scalar12487, tp12487, tm12487, ep12487, em12487, dsL]
  · norm_num [world12487, agent12487, scalar12487, tp12487, tm12487, ep12487, em12487, dsL]
  · norm_num [world12487, agent12487, scalar12487, tp12487, tm12487, ep12487, em12487, dsL]
  · norm_num [world12487, agent12487, scalar12487, tp12487, tm12487, ep12487, em12487, dsL]
  · norm_num [world12487, agent12487, scalar12487, tp12487, tm12487, ep12487, em12487, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12487, agent12487, tp12487, tm12487, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12487, agent12487, tp12487, tm12487, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12487, agent12487, scalar12487, tp12487, tm12487, ep12487, em12487, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12487, agent12487, tp12487, tm12487, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12487, agent12487, scalar12487, tp12487, tm12487, ep12487, em12487, dsL]

theorem tails12487 :
    exp (-((12487:ℝ)*ep12487)) ≤ scalar12487.upperTail ∧
    exp (-((12487:ℝ)*em12487)) ≤ scalar12487.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12487:ℝ)) (by norm_num [ep12487]) ?_)
      (show bp12487^8 ≤ scalar12487.upperTail by norm_num [bp12487, scalar12487])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12487, bp12487, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12487:ℝ)) (by norm_num [em12487]) ?_)
      (show bm12487^8 ≤ scalar12487.lowerTail by norm_num [bm12487, scalar12487])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12487, bm12487, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12487 :
    agent12487.root+dsL+scalar12487.worldRadius < √(1/100/aL) ∧
    2*(agent12487.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12487, agent12487, scalar12487, tp12487, tm12487, ep12487, em12487, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12487, agent12487, scalar12487, tp12487, tm12487, ep12487, em12487, dsL]

noncomputable def master12487 : MasterCertificate 12487 world12487 agent12487 :=
  master scalar12487 dsL tp12487 tm12487 ep12487 em12487
    (by norm_num [dsL]) (by norm_num [tp12487]) (by norm_num [tm12487])
    (by norm_num [ep12487]) (by norm_num [em12487])
    positive12487 negative12487 tails12487.1 tails12487.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12487.1 tailGuards12487.2

theorem preserves12487 : master12487.toScalarCertificate = scalar12487 := rfl

noncomputable def tp12488 : ℝ := (114800337 / 500000000)
noncomputable def tm12488 : ℝ := (-((3008681653 / 5000000000)))
noncomputable def ep12488 : ℝ := (50811420476718359 / 100000000000000000000)
noncomputable def em12488 : ℝ := (12393667732057341 / 25000000000000000000)
noncomputable def bp12488 : ℝ := (4524100710331014853 / 10000000000000000000)
noncomputable def bm12488 : ℝ := (5765362499593402823 / 12500000000000000000)

theorem positive12488 :
    Eplus aL (agent12488.root+dsL) scalar12488.worldRadius world12488.frame
      agent12488.frame tp12488 ≤ -ep12488 := by
  apply positive_check (eT := (23105301326115728233 / 20000000000000000000)) (y := (1178156965135242517 / 3125000000000000000)) (u := (145791922212219018043 / 100000000000000000000))
  · norm_num [world12488, agent12488, scalar12488, tp12488, tm12488, ep12488, em12488, dsL]
  · norm_num [world12488, agent12488, scalar12488, tp12488, tm12488, ep12488, em12488, dsL]
  · norm_num [world12488, agent12488, scalar12488, tp12488, tm12488, ep12488, em12488, dsL]
  · norm_num [world12488, agent12488, scalar12488, tp12488, tm12488, ep12488, em12488, dsL]
  · norm_num [world12488, agent12488, scalar12488, tp12488, tm12488, ep12488, em12488, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12488, agent12488, tp12488, tm12488, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12488, agent12488, scalar12488, tp12488, tm12488, ep12488, em12488, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12488, agent12488, tp12488, tm12488, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12488, agent12488, scalar12488, tp12488, tm12488, ep12488, em12488, dsL]

theorem negative12488 :
    Eminus aL (agent12488.root+dsL) scalar12488.worldRadius world12488.frame
      agent12488.frame tm12488 ≤ -em12488 := by
  apply negative_check (lo := (17126328439686347711 / 25000000000000000000)) (hi := (13701062751749078169 / 20000000000000000000))
    (y := (-((71705233443884592263 / 100000000000000000000)))) (u := (48818915553096622109 / 100000000000000000000))
  · norm_num [world12488, agent12488, scalar12488, tp12488, tm12488, ep12488, em12488, dsL]
  · norm_num [world12488, agent12488, scalar12488, tp12488, tm12488, ep12488, em12488, dsL]
  · norm_num [world12488, agent12488, scalar12488, tp12488, tm12488, ep12488, em12488, dsL]
  · norm_num [world12488, agent12488, scalar12488, tp12488, tm12488, ep12488, em12488, dsL]
  · norm_num [world12488, agent12488, scalar12488, tp12488, tm12488, ep12488, em12488, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12488, agent12488, tp12488, tm12488, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12488, agent12488, tp12488, tm12488, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12488, agent12488, scalar12488, tp12488, tm12488, ep12488, em12488, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12488, agent12488, tp12488, tm12488, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12488, agent12488, scalar12488, tp12488, tm12488, ep12488, em12488, dsL]

theorem tails12488 :
    exp (-((12488:ℝ)*ep12488)) ≤ scalar12488.upperTail ∧
    exp (-((12488:ℝ)*em12488)) ≤ scalar12488.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12488:ℝ)) (by norm_num [ep12488]) ?_)
      (show bp12488^8 ≤ scalar12488.upperTail by norm_num [bp12488, scalar12488])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12488, bp12488, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12488:ℝ)) (by norm_num [em12488]) ?_)
      (show bm12488^8 ≤ scalar12488.lowerTail by norm_num [bm12488, scalar12488])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12488, bm12488, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12488 :
    agent12488.root+dsL+scalar12488.worldRadius < √(1/100/aL) ∧
    2*(agent12488.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12488, agent12488, scalar12488, tp12488, tm12488, ep12488, em12488, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12488, agent12488, scalar12488, tp12488, tm12488, ep12488, em12488, dsL]

noncomputable def master12488 : MasterCertificate 12488 world12488 agent12488 :=
  master scalar12488 dsL tp12488 tm12488 ep12488 em12488
    (by norm_num [dsL]) (by norm_num [tp12488]) (by norm_num [tm12488])
    (by norm_num [ep12488]) (by norm_num [em12488])
    positive12488 negative12488 tails12488.1 tails12488.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12488.1 tailGuards12488.2

theorem preserves12488 : master12488.toScalarCertificate = scalar12488 := rfl

noncomputable def tp12489 : ℝ := (2296099093 / 10000000000)
noncomputable def tm12489 : ℝ := (-((6017562923 / 10000000000)))
noncomputable def ep12489 : ℝ := (25407142608952453 / 50000000000000000000)
noncomputable def em12489 : ℝ := (49577143651271643 / 100000000000000000000)
noncomputable def bp12489 : ℝ := (45236110641555540577 / 100000000000000000000)
noncomputable def bm12489 : ℝ := (23059130810297398543 / 50000000000000000000)

theorem positive12489 :
    Eplus aL (agent12489.root+dsL) scalar12489.worldRadius world12489.frame
      agent12489.frame tp12489 ≤ -ep12489 := by
  apply positive_check (eT := (115526797296496413397 / 100000000000000000000)) (y := (37701890380699971971 / 100000000000000000000)) (u := (72896593478670493721 / 50000000000000000000))
  · norm_num [world12489, agent12489, scalar12489, tp12489, tm12489, ep12489, em12489, dsL]
  · norm_num [world12489, agent12489, scalar12489, tp12489, tm12489, ep12489, em12489, dsL]
  · norm_num [world12489, agent12489, scalar12489, tp12489, tm12489, ep12489, em12489, dsL]
  · norm_num [world12489, agent12489, scalar12489, tp12489, tm12489, ep12489, em12489, dsL]
  · norm_num [world12489, agent12489, scalar12489, tp12489, tm12489, ep12489, em12489, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12489, agent12489, tp12489, tm12489, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12489, agent12489, scalar12489, tp12489, tm12489, ep12489, em12489, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12489, agent12489, tp12489, tm12489, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12489, agent12489, scalar12489, tp12489, tm12489, ep12489, em12489, dsL]

theorem negative12489 :
    Eminus aL (agent12489.root+dsL) scalar12489.worldRadius world12489.frame
      agent12489.frame tm12489 ≤ -em12489 := by
  apply negative_check (lo := (6850504471519606987 / 10000000000000000000)) (hi := (68505044715196069871 / 100000000000000000000))
    (y := (-((35852695600963141093 / 50000000000000000000)))) (u := (6102354817174027567 / 12500000000000000000))
  · norm_num [world12489, agent12489, scalar12489, tp12489, tm12489, ep12489, em12489, dsL]
  · norm_num [world12489, agent12489, scalar12489, tp12489, tm12489, ep12489, em12489, dsL]
  · norm_num [world12489, agent12489, scalar12489, tp12489, tm12489, ep12489, em12489, dsL]
  · norm_num [world12489, agent12489, scalar12489, tp12489, tm12489, ep12489, em12489, dsL]
  · norm_num [world12489, agent12489, scalar12489, tp12489, tm12489, ep12489, em12489, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12489, agent12489, tp12489, tm12489, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12489, agent12489, tp12489, tm12489, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12489, agent12489, scalar12489, tp12489, tm12489, ep12489, em12489, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12489, agent12489, tp12489, tm12489, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12489, agent12489, scalar12489, tp12489, tm12489, ep12489, em12489, dsL]

theorem tails12489 :
    exp (-((12489:ℝ)*ep12489)) ≤ scalar12489.upperTail ∧
    exp (-((12489:ℝ)*em12489)) ≤ scalar12489.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12489:ℝ)) (by norm_num [ep12489]) ?_)
      (show bp12489^8 ≤ scalar12489.upperTail by norm_num [bp12489, scalar12489])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12489, bp12489, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12489:ℝ)) (by norm_num [em12489]) ?_)
      (show bm12489^8 ≤ scalar12489.lowerTail by norm_num [bm12489, scalar12489])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12489, bm12489, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12489 :
    agent12489.root+dsL+scalar12489.worldRadius < √(1/100/aL) ∧
    2*(agent12489.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12489, agent12489, scalar12489, tp12489, tm12489, ep12489, em12489, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12489, agent12489, scalar12489, tp12489, tm12489, ep12489, em12489, dsL]

noncomputable def master12489 : MasterCertificate 12489 world12489 agent12489 :=
  master scalar12489 dsL tp12489 tm12489 ep12489 em12489
    (by norm_num [dsL]) (by norm_num [tp12489]) (by norm_num [tm12489])
    (by norm_num [ep12489]) (by norm_num [em12489])
    positive12489 negative12489 tails12489.1 tails12489.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12489.1 tailGuards12489.2

theorem preserves12489 : master12489.toScalarCertificate = scalar12489 := rfl

noncomputable def tp12490 : ℝ := (2296267699 / 10000000000)
noncomputable def tm12490 : ℝ := (-((3008996423 / 5000000000)))
noncomputable def ep12490 : ℝ := (10163723037755131 / 20000000000000000000)
noncomputable def em12490 : ℝ := (12395302649621051 / 25000000000000000000)
noncomputable def bp12490 : ℝ := (11307544923244163991 / 25000000000000000000)
noncomputable def bm12490 : ℝ := (46112475680110800101 / 100000000000000000000)

theorem positive12490 :
    Eplus aL (agent12490.root+dsL) scalar12490.worldRadius world12490.frame
      agent12490.frame tp12490 ≤ -ep12490 := by
  apply positive_check (eT := (115527641733506755363 / 100000000000000000000)) (y := (2356376652450935241 / 6250000000000000000)) (u := (145793385321521066591 / 100000000000000000000))
  · norm_num [world12490, agent12490, scalar12490, tp12490, tm12490, ep12490, em12490, dsL]
  · norm_num [world12490, agent12490, scalar12490, tp12490, tm12490, ep12490, em12490, dsL]
  · norm_num [world12490, agent12490, scalar12490, tp12490, tm12490, ep12490, em12490, dsL]
  · norm_num [world12490, agent12490, scalar12490, tp12490, tm12490, ep12490, em12490, dsL]
  · norm_num [world12490, agent12490, scalar12490, tp12490, tm12490, ep12490, em12490, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12490, agent12490, tp12490, tm12490, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12490, agent12490, scalar12490, tp12490, tm12490, ep12490, em12490, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12490, agent12490, tp12490, tm12490, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12490, agent12490, scalar12490, tp12490, tm12490, ep12490, em12490, dsL]

theorem negative12490 :
    Eminus aL (agent12490.root+dsL) scalar12490.worldRadius world12490.frame
      agent12490.frame tm12490 ≤ -em12490 := by
  apply negative_check (lo := (1370075678042206147 / 2000000000000000000)) (hi := (68503783902110307351 / 100000000000000000000))
    (y := (-((71703616929236947267 / 100000000000000000000)))) (u := (9763940944879175399 / 20000000000000000000))
  · norm_num [world12490, agent12490, scalar12490, tp12490, tm12490, ep12490, em12490, dsL]
  · norm_num [world12490, agent12490, scalar12490, tp12490, tm12490, ep12490, em12490, dsL]
  · norm_num [world12490, agent12490, scalar12490, tp12490, tm12490, ep12490, em12490, dsL]
  · norm_num [world12490, agent12490, scalar12490, tp12490, tm12490, ep12490, em12490, dsL]
  · norm_num [world12490, agent12490, scalar12490, tp12490, tm12490, ep12490, em12490, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12490, agent12490, tp12490, tm12490, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12490, agent12490, tp12490, tm12490, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12490, agent12490, scalar12490, tp12490, tm12490, ep12490, em12490, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12490, agent12490, tp12490, tm12490, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12490, agent12490, scalar12490, tp12490, tm12490, ep12490, em12490, dsL]

theorem tails12490 :
    exp (-((12490:ℝ)*ep12490)) ≤ scalar12490.upperTail ∧
    exp (-((12490:ℝ)*em12490)) ≤ scalar12490.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12490:ℝ)) (by norm_num [ep12490]) ?_)
      (show bp12490^8 ≤ scalar12490.upperTail by norm_num [bp12490, scalar12490])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12490, bp12490, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12490:ℝ)) (by norm_num [em12490]) ?_)
      (show bm12490^8 ≤ scalar12490.lowerTail by norm_num [bm12490, scalar12490])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12490, bm12490, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12490 :
    agent12490.root+dsL+scalar12490.worldRadius < √(1/100/aL) ∧
    2*(agent12490.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12490, agent12490, scalar12490, tp12490, tm12490, ep12490, em12490, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12490, agent12490, scalar12490, tp12490, tm12490, ep12490, em12490, dsL]

noncomputable def master12490 : MasterCertificate 12490 world12490 agent12490 :=
  master scalar12490 dsL tp12490 tm12490 ep12490 em12490
    (by norm_num [dsL]) (by norm_num [tp12490]) (by norm_num [tm12490])
    (by norm_num [ep12490]) (by norm_num [em12490])
    positive12490 negative12490 tails12490.1 tails12490.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12490.1 tailGuards12490.2

theorem preserves12490 : master12490.toScalarCertificate = scalar12490 := rfl

noncomputable def tp12491 : ℝ := (91854399 / 400000000)
noncomputable def tm12491 : ℝ := (-((240727693 / 400000000)))
noncomputable def ep12491 : ℝ := (25410738375189251 / 50000000000000000000)
noncomputable def em12491 : ℝ := (49583680376985453 / 100000000000000000000)
noncomputable def bp12491 : ℝ := (45225285917673247327 / 100000000000000000000)
noncomputable def bm12491 : ℝ := (46107839810166447279 / 100000000000000000000)

theorem positive12491 :
    Eplus aL (agent12491.root+dsL) scalar12491.worldRadius world12491.frame
      agent12491.frame tp12491 ≤ -ep12491 := by
  apply positive_check (eT := (57763965946909217571 / 50000000000000000000)) (y := (4712861675906076069 / 12500000000000000000)) (u := (36448662327261537149 / 25000000000000000000))
  · norm_num [world12491, agent12491, scalar12491, tp12491, tm12491, ep12491, em12491, dsL]
  · norm_num [world12491, agent12491, scalar12491, tp12491, tm12491, ep12491, em12491, dsL]
  · norm_num [world12491, agent12491, scalar12491, tp12491, tm12491, ep12491, em12491, dsL]
  · norm_num [world12491, agent12491, scalar12491, tp12491, tm12491, ep12491, em12491, dsL]
  · norm_num [world12491, agent12491, scalar12491, tp12491, tm12491, ep12491, em12491, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12491, agent12491, tp12491, tm12491, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12491, agent12491, scalar12491, tp12491, tm12491, ep12491, em12491, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12491, agent12491, tp12491, tm12491, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12491, agent12491, scalar12491, tp12491, tm12491, ep12491, em12491, dsL]

theorem negative12491 :
    Eminus aL (agent12491.root+dsL) scalar12491.worldRadius world12491.frame
      agent12491.frame tm12491 ≤ -em12491 := by
  apply negative_check (lo := (68503515366351241549 / 100000000000000000000)) (hi := (1370070307327024831 / 2000000000000000000))
    (y := (-((2240742958067856391 / 3125000000000000000)))) (u := (6102453465207067231 / 12500000000000000000))
  · norm_num [world12491, agent12491, scalar12491, tp12491, tm12491, ep12491, em12491, dsL]
  · norm_num [world12491, agent12491, scalar12491, tp12491, tm12491, ep12491, em12491, dsL]
  · norm_num [world12491, agent12491, scalar12491, tp12491, tm12491, ep12491, em12491, dsL]
  · norm_num [world12491, agent12491, scalar12491, tp12491, tm12491, ep12491, em12491, dsL]
  · norm_num [world12491, agent12491, scalar12491, tp12491, tm12491, ep12491, em12491, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12491, agent12491, tp12491, tm12491, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12491, agent12491, tp12491, tm12491, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12491, agent12491, scalar12491, tp12491, tm12491, ep12491, em12491, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12491, agent12491, tp12491, tm12491, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12491, agent12491, scalar12491, tp12491, tm12491, ep12491, em12491, dsL]

theorem tails12491 :
    exp (-((12491:ℝ)*ep12491)) ≤ scalar12491.upperTail ∧
    exp (-((12491:ℝ)*em12491)) ≤ scalar12491.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12491:ℝ)) (by norm_num [ep12491]) ?_)
      (show bp12491^8 ≤ scalar12491.upperTail by norm_num [bp12491, scalar12491])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12491, bp12491, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12491:ℝ)) (by norm_num [em12491]) ?_)
      (show bm12491^8 ≤ scalar12491.lowerTail by norm_num [bm12491, scalar12491])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12491, bm12491, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12491 :
    agent12491.root+dsL+scalar12491.worldRadius < √(1/100/aL) ∧
    2*(agent12491.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12491, agent12491, scalar12491, tp12491, tm12491, ep12491, em12491, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12491, agent12491, scalar12491, tp12491, tm12491, ep12491, em12491, dsL]

noncomputable def master12491 : MasterCertificate 12491 world12491 agent12491 :=
  master scalar12491 dsL tp12491 tm12491 ep12491 em12491
    (by norm_num [dsL]) (by norm_num [tp12491]) (by norm_num [tm12491])
    (by norm_num [ep12491]) (by norm_num [em12491])
    positive12491 negative12491 tails12491.1 tails12491.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12491.1 tailGuards12491.2

theorem preserves12491 : master12491.toScalarCertificate = scalar12491 := rfl

noncomputable def tp12492 : ℝ := (574113047 / 2500000000)
noncomputable def tm12492 : ℝ := (-((3009195823 / 5000000000)))
noncomputable def ep12492 : ℝ := (25412168651989561 / 50000000000000000000)
noncomputable def em12492 : ℝ := (49586149209533341 / 100000000000000000000)
noncomputable def bp12492 : ℝ := (22610196530063417343 / 50000000000000000000)
noncomputable def bm12492 : ℝ := (2881450300163499769 / 6250000000000000000)

theorem positive12492 :
    Eplus aL (agent12492.root+dsL) scalar12492.worldRadius world12492.frame
      agent12492.frame tp12492 ≤ -ep12492 := by
  apply positive_check (eT := (28882055407251348941 / 25000000000000000000)) (y := (37703759727923742091 / 100000000000000000000)) (u := (29159182472741479047 / 20000000000000000000))
  · norm_num [world12492, agent12492, scalar12492, tp12492, tm12492, ep12492, em12492, dsL]
  · norm_num [world12492, agent12492, scalar12492, tp12492, tm12492, ep12492, em12492, dsL]
  · norm_num [world12492, agent12492, scalar12492, tp12492, tm12492, ep12492, em12492, dsL]
  · norm_num [world12492, agent12492, scalar12492, tp12492, tm12492, ep12492, em12492, dsL]
  · norm_num [world12492, agent12492, scalar12492, tp12492, tm12492, ep12492, em12492, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12492, agent12492, tp12492, tm12492, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12492, agent12492, scalar12492, tp12492, tm12492, ep12492, em12492, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12492, agent12492, tp12492, tm12492, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12492, agent12492, scalar12492, tp12492, tm12492, ep12492, em12492, dsL]

theorem negative12492 :
    Eminus aL (agent12492.root+dsL) scalar12492.worldRadius world12492.frame
      agent12492.frame tm12492 ≤ -em12492 := by
  apply negative_check (lo := (34251623727252723573 / 50000000000000000000)) (hi := (68503247454505447147 / 100000000000000000000))
    (y := (-((35851965950128911263 / 50000000000000000000)))) (u := (24409775478357840111 / 50000000000000000000))
  · norm_num [world12492, agent12492, scalar12492, tp12492, tm12492, ep12492, em12492, dsL]
  · norm_num [world12492, agent12492, scalar12492, tp12492, tm12492, ep12492, em12492, dsL]
  · norm_num [world12492, agent12492, scalar12492, tp12492, tm12492, ep12492, em12492, dsL]
  · norm_num [world12492, agent12492, scalar12492, tp12492, tm12492, ep12492, em12492, dsL]
  · norm_num [world12492, agent12492, scalar12492, tp12492, tm12492, ep12492, em12492, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12492, agent12492, tp12492, tm12492, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12492, agent12492, tp12492, tm12492, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12492, agent12492, scalar12492, tp12492, tm12492, ep12492, em12492, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12492, agent12492, tp12492, tm12492, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12492, agent12492, scalar12492, tp12492, tm12492, ep12492, em12492, dsL]

theorem tails12492 :
    exp (-((12492:ℝ)*ep12492)) ≤ scalar12492.upperTail ∧
    exp (-((12492:ℝ)*em12492)) ≤ scalar12492.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12492:ℝ)) (by norm_num [ep12492]) ?_)
      (show bp12492^8 ≤ scalar12492.upperTail by norm_num [bp12492, scalar12492])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12492, bp12492, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12492:ℝ)) (by norm_num [em12492]) ?_)
      (show bm12492^8 ≤ scalar12492.lowerTail by norm_num [bm12492, scalar12492])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12492, bm12492, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12492 :
    agent12492.root+dsL+scalar12492.worldRadius < √(1/100/aL) ∧
    2*(agent12492.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12492, agent12492, scalar12492, tp12492, tm12492, ep12492, em12492, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12492, agent12492, scalar12492, tp12492, tm12492, ep12492, em12492, dsL]

noncomputable def master12492 : MasterCertificate 12492 world12492 agent12492 :=
  master scalar12492 dsL tp12492 tm12492 ep12492 em12492
    (by norm_num [dsL]) (by norm_num [tp12492]) (by norm_num [tm12492])
    (by norm_num [ep12492]) (by norm_num [em12492])
    positive12492 negative12492 tails12492.1 tails12492.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12492.1 tailGuards12492.2

theorem preserves12492 : master12492.toScalarCertificate = scalar12492 := rfl

noncomputable def tp12493 : ℝ := (2296544461 / 10000000000)
noncomputable def tm12493 : ℝ := (-((3009295401 / 5000000000)))
noncomputable def ep12493 : ℝ := (1588349881086903 / 3125000000000000000)
noncomputable def em12493 : ℝ := (24794308265519603 / 50000000000000000000)
noncomputable def bp12493 : ℝ := (113038753956686687 / 250000000000000000)
noncomputable def bm12493 : ℝ := (23049285532128233627 / 50000000000000000000)

theorem positive12493 :
    Eplus aL (agent12493.root+dsL) scalar12493.worldRadius world12493.frame
      agent12493.frame tp12493 ≤ -ep12493 := by
  apply positive_check (eT := (3610265994759782447 / 3125000000000000000)) (y := (7540925493192433053 / 20000000000000000000)) (u := (36449294373946612361 / 25000000000000000000))
  · norm_num [world12493, agent12493, scalar12493, tp12493, tm12493, ep12493, em12493, dsL]
  · norm_num [world12493, agent12493, scalar12493, tp12493, tm12493, ep12493, em12493, dsL]
  · norm_num [world12493, agent12493, scalar12493, tp12493, tm12493, ep12493, em12493, dsL]
  · norm_num [world12493, agent12493, scalar12493, tp12493, tm12493, ep12493, em12493, dsL]
  · norm_num [world12493, agent12493, scalar12493, tp12493, tm12493, ep12493, em12493, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12493, agent12493, tp12493, tm12493, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12493, agent12493, scalar12493, tp12493, tm12493, ep12493, em12493, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12493, agent12493, tp12493, tm12493, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12493, agent12493, scalar12493, tp12493, tm12493, ep12493, em12493, dsL]

theorem negative12493 :
    Eminus aL (agent12493.root+dsL) scalar12493.worldRadius world12493.frame
      agent12493.frame tm12493 ≤ -em12493 := by
  apply negative_check (lo := (68502980196566900167 / 100000000000000000000)) (hi := (8562872524570862521 / 12500000000000000000))
    (y := (-((8963011020835873389 / 12500000000000000000)))) (u := (48819474668206272657 / 100000000000000000000))
  · norm_num [world12493, agent12493, scalar12493, tp12493, tm12493, ep12493, em12493, dsL]
  · norm_num [world12493, agent12493, scalar12493, tp12493, tm12493, ep12493, em12493, dsL]
  · norm_num [world12493, agent12493, scalar12493, tp12493, tm12493, ep12493, em12493, dsL]
  · norm_num [world12493, agent12493, scalar12493, tp12493, tm12493, ep12493, em12493, dsL]
  · norm_num [world12493, agent12493, scalar12493, tp12493, tm12493, ep12493, em12493, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12493, agent12493, tp12493, tm12493, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12493, agent12493, tp12493, tm12493, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12493, agent12493, scalar12493, tp12493, tm12493, ep12493, em12493, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12493, agent12493, tp12493, tm12493, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12493, agent12493, scalar12493, tp12493, tm12493, ep12493, em12493, dsL]

theorem tails12493 :
    exp (-((12493:ℝ)*ep12493)) ≤ scalar12493.upperTail ∧
    exp (-((12493:ℝ)*em12493)) ≤ scalar12493.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12493:ℝ)) (by norm_num [ep12493]) ?_)
      (show bp12493^8 ≤ scalar12493.upperTail by norm_num [bp12493, scalar12493])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12493, bp12493, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12493:ℝ)) (by norm_num [em12493]) ?_)
      (show bm12493^8 ≤ scalar12493.lowerTail by norm_num [bm12493, scalar12493])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12493, bm12493, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12493 :
    agent12493.root+dsL+scalar12493.worldRadius < √(1/100/aL) ∧
    2*(agent12493.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12493, agent12493, scalar12493, tp12493, tm12493, ep12493, em12493, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12493, agent12493, scalar12493, tp12493, tm12493, ep12493, em12493, dsL]

noncomputable def master12493 : MasterCertificate 12493 world12493 agent12493 :=
  master scalar12493 dsL tp12493 tm12493 ep12493 em12493
    (by norm_num [dsL]) (by norm_num [tp12493]) (by norm_num [tm12493])
    (by norm_num [ep12493]) (by norm_num [em12493])
    positive12493 negative12493 tails12493.1 tails12493.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12493.1 tailGuards12493.2

theorem preserves12493 : master12493.toScalarCertificate = scalar12493 := rfl

noncomputable def tp12494 : ℝ := (459327329 / 2000000000)
noncomputable def tm12494 : ℝ := (-((6018789947 / 10000000000)))
noncomputable def ep12494 : ℝ := (25415027034859221 / 50000000000000000000)
noncomputable def em12494 : ℝ := (12397770723423689 / 25000000000000000000)
noncomputable def bp12494 : ℝ := (22605305514239930293 / 50000000000000000000)
noncomputable def bm12494 : ℝ := (46093938197552613249 / 100000000000000000000)

theorem positive12494 :
    Eplus aL (agent12494.root+dsL) scalar12494.worldRadius world12494.frame
      agent12494.frame tp12494 ≤ -ep12494 := by
  apply positive_check (eT := (115528801421737312209 / 100000000000000000000)) (y := (37705493995945254411 / 100000000000000000000)) (u := (7289922043875886549 / 5000000000000000000))
  · norm_num [world12494, agent12494, scalar12494, tp12494, tm12494, ep12494, em12494, dsL]
  · norm_num [world12494, agent12494, scalar12494, tp12494, tm12494, ep12494, em12494, dsL]
  · norm_num [world12494, agent12494, scalar12494, tp12494, tm12494, ep12494, em12494, dsL]
  · norm_num [world12494, agent12494, scalar12494, tp12494, tm12494, ep12494, em12494, dsL]
  · norm_num [world12494, agent12494, scalar12494, tp12494, tm12494, ep12494, em12494, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12494, agent12494, tp12494, tm12494, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12494, agent12494, scalar12494, tp12494, tm12494, ep12494, em12494, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12494, agent12494, tp12494, tm12494, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12494, agent12494, scalar12494, tp12494, tm12494, ep12494, em12494, dsL]

theorem negative12494 :
    Eminus aL (agent12494.root+dsL) scalar12494.worldRadius world12494.frame
      agent12494.frame tm12494 ≤ -em12494 := by
  apply negative_check (lo := (68502712929493512047 / 100000000000000000000)) (hi := (4281419558093344503 / 6250000000000000000))
    (y := (-((71704244973159806827 / 100000000000000000000)))) (u := (24409699058085007809 / 50000000000000000000))
  · norm_num [world12494, agent12494, scalar12494, tp12494, tm12494, ep12494, em12494, dsL]
  · norm_num [world12494, agent12494, scalar12494, tp12494, tm12494, ep12494, em12494, dsL]
  · norm_num [world12494, agent12494, scalar12494, tp12494, tm12494, ep12494, em12494, dsL]
  · norm_num [world12494, agent12494, scalar12494, tp12494, tm12494, ep12494, em12494, dsL]
  · norm_num [world12494, agent12494, scalar12494, tp12494, tm12494, ep12494, em12494, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12494, agent12494, tp12494, tm12494, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12494, agent12494, tp12494, tm12494, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12494, agent12494, scalar12494, tp12494, tm12494, ep12494, em12494, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12494, agent12494, tp12494, tm12494, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12494, agent12494, scalar12494, tp12494, tm12494, ep12494, em12494, dsL]

theorem tails12494 :
    exp (-((12494:ℝ)*ep12494)) ≤ scalar12494.upperTail ∧
    exp (-((12494:ℝ)*em12494)) ≤ scalar12494.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12494:ℝ)) (by norm_num [ep12494]) ?_)
      (show bp12494^8 ≤ scalar12494.upperTail by norm_num [bp12494, scalar12494])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12494, bp12494, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12494:ℝ)) (by norm_num [em12494]) ?_)
      (show bm12494^8 ≤ scalar12494.lowerTail by norm_num [bm12494, scalar12494])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12494, bm12494, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12494 :
    agent12494.root+dsL+scalar12494.worldRadius < √(1/100/aL) ∧
    2*(agent12494.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12494, agent12494, scalar12494, tp12494, tm12494, ep12494, em12494, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12494, agent12494, scalar12494, tp12494, tm12494, ep12494, em12494, dsL]

noncomputable def master12494 : MasterCertificate 12494 world12494 agent12494 :=
  master scalar12494 dsL tp12494 tm12494 ep12494 em12494
    (by norm_num [dsL]) (by norm_num [tp12494]) (by norm_num [tm12494])
    (by norm_num [ep12494]) (by norm_num [em12494])
    positive12494 negative12494 tails12494.1 tails12494.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12494.1 tailGuards12494.2

theorem preserves12494 : master12494.toScalarCertificate = scalar12494 := rfl

noncomputable def tp12495 : ℝ := (287091091 / 1250000000)
noncomputable def tm12495 : ℝ := (-((1504747239 / 2500000000)))
noncomputable def ep12495 : ℝ := (25416454930516469 / 50000000000000000000)
noncomputable def em12495 : ℝ := (49593547298789717 / 100000000000000000000)
noncomputable def bp12495 : ℝ := (45205722151427923509 / 100000000000000000000)
noncomputable def bm12495 : ℝ := (23044653460714949797 / 50000000000000000000)

theorem positive12495 :
    Eplus aL (agent12495.root+dsL) scalar12495.worldRadius world12495.frame
      agent12495.frame tp12495 ≤ -ep12495 := by
  apply positive_check (eT := (57764545155095761159 / 50000000000000000000)) (y := (9426589864228266193 / 25000000000000000000)) (u := (145799702711575534711 / 100000000000000000000))
  · norm_num [world12495, agent12495, scalar12495, tp12495, tm12495, ep12495, em12495, dsL]
  · norm_num [world12495, agent12495, scalar12495, tp12495, tm12495, ep12495, em12495, dsL]
  · norm_num [world12495, agent12495, scalar12495, tp12495, tm12495, ep12495, em12495, dsL]
  · norm_num [world12495, agent12495, scalar12495, tp12495, tm12495, ep12495, em12495, dsL]
  · norm_num [world12495, agent12495, scalar12495, tp12495, tm12495, ep12495, em12495, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12495, agent12495, tp12495, tm12495, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12495, agent12495, scalar12495, tp12495, tm12495, ep12495, em12495, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12495, agent12495, tp12495, tm12495, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12495, agent12495, scalar12495, tp12495, tm12495, ep12495, em12495, dsL]

theorem negative12495 :
    Eminus aL (agent12495.root+dsL) scalar12495.worldRadius world12495.frame
      agent12495.frame tm12495 ≤ -em12495 := by
  apply negative_check (lo := (68502446191455262981 / 100000000000000000000)) (hi := (34251223095727631491 / 50000000000000000000))
    (y := (-((35852200769321442763 / 50000000000000000000)))) (u := (24409660840951676889 / 50000000000000000000))
  · norm_num [world12495, agent12495, scalar12495, tp12495, tm12495, ep12495, em12495, dsL]
  · norm_num [world12495, agent12495, scalar12495, tp12495, tm12495, ep12495, em12495, dsL]
  · norm_num [world12495, agent12495, scalar12495, tp12495, tm12495, ep12495, em12495, dsL]
  · norm_num [world12495, agent12495, scalar12495, tp12495, tm12495, ep12495, em12495, dsL]
  · norm_num [world12495, agent12495, scalar12495, tp12495, tm12495, ep12495, em12495, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12495, agent12495, tp12495, tm12495, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12495, agent12495, tp12495, tm12495, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12495, agent12495, scalar12495, tp12495, tm12495, ep12495, em12495, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12495, agent12495, tp12495, tm12495, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12495, agent12495, scalar12495, tp12495, tm12495, ep12495, em12495, dsL]

theorem tails12495 :
    exp (-((12495:ℝ)*ep12495)) ≤ scalar12495.upperTail ∧
    exp (-((12495:ℝ)*em12495)) ≤ scalar12495.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12495:ℝ)) (by norm_num [ep12495]) ?_)
      (show bp12495^8 ≤ scalar12495.upperTail by norm_num [bp12495, scalar12495])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12495, bp12495, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12495:ℝ)) (by norm_num [em12495]) ?_)
      (show bm12495^8 ≤ scalar12495.lowerTail by norm_num [bm12495, scalar12495])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12495, bm12495, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12495 :
    agent12495.root+dsL+scalar12495.worldRadius < √(1/100/aL) ∧
    2*(agent12495.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12495, agent12495, scalar12495, tp12495, tm12495, ep12495, em12495, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12495, agent12495, scalar12495, tp12495, tm12495, ep12495, em12495, dsL]

noncomputable def master12495 : MasterCertificate 12495 world12495 agent12495 :=
  master scalar12495 dsL tp12495 tm12495 ep12495 em12495
    (by norm_num [dsL]) (by norm_num [tp12495]) (by norm_num [tm12495])
    (by norm_num [ep12495]) (by norm_num [em12495])
    positive12495 negative12495 tails12495.1 tails12495.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12495.1 tailGuards12495.2

theorem preserves12495 : master12495.toScalarCertificate = scalar12495 := rfl

noncomputable def tp12496 : ℝ := (2296820803 / 10000000000)
noncomputable def tm12496 : ℝ := (-((752398493 / 1250000000)))
noncomputable def ep12496 : ℝ := (50835764457298009 / 100000000000000000000)
noncomputable def em12496 : ℝ := (24798005312792647 / 50000000000000000000)
noncomputable def bp12496 : ℝ := (11300208581019116291 / 25000000000000000000)
noncomputable def bm12496 : ℝ := (11521169150727754767 / 25000000000000000000)

theorem positive12496 :
    Eplus aL (agent12496.root+dsL) scalar12496.worldRadius world12496.frame
      agent12496.frame tp12496 ≤ -ep12496 := by
  apply positive_check (eT := (115529379172974055767 / 100000000000000000000)) (y := (37707225086904471073 / 100000000000000000000)) (u := (36450241200748025091 / 25000000000000000000))
  · norm_num [world12496, agent12496, scalar12496, tp12496, tm12496, ep12496, em12496, dsL]
  · norm_num [world12496, agent12496, scalar12496, tp12496, tm12496, ep12496, em12496, dsL]
  · norm_num [world12496, agent12496, scalar12496, tp12496, tm12496, ep12496, em12496, dsL]
  · norm_num [world12496, agent12496, scalar12496, tp12496, tm12496, ep12496, em12496, dsL]
  · norm_num [world12496, agent12496, scalar12496, tp12496, tm12496, ep12496, em12496, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12496, agent12496, tp12496, tm12496, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12496, agent12496, scalar12496, tp12496, tm12496, ep12496, em12496, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12496, agent12496, tp12496, tm12496, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12496, agent12496, scalar12496, tp12496, tm12496, ep12496, em12496, dsL]

theorem negative12496 :
    Eminus aL (agent12496.root+dsL) scalar12496.worldRadius world12496.frame
      agent12496.frame tm12496 ≤ -em12496 := by
  apply negative_check (lo := (68502179487322753089 / 100000000000000000000)) (hi := (6850217948732275309 / 10000000000000000000))
    (y := (-((3585227933348553213 / 5000000000000000000)))) (u := (24409622486489816273 / 50000000000000000000))
  · norm_num [world12496, agent12496, scalar12496, tp12496, tm12496, ep12496, em12496, dsL]
  · norm_num [world12496, agent12496, scalar12496, tp12496, tm12496, ep12496, em12496, dsL]
  · norm_num [world12496, agent12496, scalar12496, tp12496, tm12496, ep12496, em12496, dsL]
  · norm_num [world12496, agent12496, scalar12496, tp12496, tm12496, ep12496, em12496, dsL]
  · norm_num [world12496, agent12496, scalar12496, tp12496, tm12496, ep12496, em12496, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12496, agent12496, tp12496, tm12496, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12496, agent12496, tp12496, tm12496, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12496, agent12496, scalar12496, tp12496, tm12496, ep12496, em12496, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12496, agent12496, tp12496, tm12496, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12496, agent12496, scalar12496, tp12496, tm12496, ep12496, em12496, dsL]

theorem tails12496 :
    exp (-((12496:ℝ)*ep12496)) ≤ scalar12496.upperTail ∧
    exp (-((12496:ℝ)*em12496)) ≤ scalar12496.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12496:ℝ)) (by norm_num [ep12496]) ?_)
      (show bp12496^8 ≤ scalar12496.upperTail by norm_num [bp12496, scalar12496])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12496, bp12496, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12496:ℝ)) (by norm_num [em12496]) ?_)
      (show bm12496^8 ≤ scalar12496.lowerTail by norm_num [bm12496, scalar12496])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12496, bm12496, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12496 :
    agent12496.root+dsL+scalar12496.worldRadius < √(1/100/aL) ∧
    2*(agent12496.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12496, agent12496, scalar12496, tp12496, tm12496, ep12496, em12496, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12496, agent12496, scalar12496, tp12496, tm12496, ep12496, em12496, dsL]

noncomputable def master12496 : MasterCertificate 12496 world12496 agent12496 :=
  master scalar12496 dsL tp12496 tm12496 ep12496 em12496
    (by norm_num [dsL]) (by norm_num [tp12496]) (by norm_num [tm12496])
    (by norm_num [ep12496]) (by norm_num [em12496])
    positive12496 negative12496 tails12496.1 tails12496.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12496.1 tailGuards12496.2

theorem preserves12496 : master12496.toScalarCertificate = scalar12496 := rfl

noncomputable def tp12497 : ℝ := (2296912829 / 10000000000)
noncomputable def tm12497 : ℝ := (-((6019386693 / 10000000000)))
noncomputable def ep12497 : ℝ := (2541930878749357 / 5000000000000000000)
noncomputable def em12497 : ℝ := (49598472565420607 / 100000000000000000000)
noncomputable def bp12497 : ℝ := (22597973873288223017 / 50000000000000000000)
noncomputable def bm12497 : ℝ := (46080047464169905181 / 100000000000000000000)

theorem positive12497 :
    Eplus aL (agent12497.root+dsL) scalar12497.worldRadius world12497.frame
      agent12497.frame tp12497 ≤ -ep12497 := by
  apply positive_check (eT := (28882416928093706827 / 25000000000000000000)) (y := (37708090262206887463 / 100000000000000000000)) (u := (145802226242387083847 / 100000000000000000000))
  · norm_num [world12497, agent12497, scalar12497, tp12497, tm12497, ep12497, em12497, dsL]
  · norm_num [world12497, agent12497, scalar12497, tp12497, tm12497, ep12497, em12497, dsL]
  · norm_num [world12497, agent12497, scalar12497, tp12497, tm12497, ep12497, em12497, dsL]
  · norm_num [world12497, agent12497, scalar12497, tp12497, tm12497, ep12497, em12497, dsL]
  · norm_num [world12497, agent12497, scalar12497, tp12497, tm12497, ep12497, em12497, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12497, agent12497, tp12497, tm12497, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12497, agent12497, scalar12497, tp12497, tm12497, ep12497, em12497, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12497, agent12497, tp12497, tm12497, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12497, agent12497, scalar12497, tp12497, tm12497, ep12497, em12497, dsL]

theorem negative12497 :
    Eminus aL (agent12497.root+dsL) scalar12497.worldRadius world12497.frame
      agent12497.frame tm12497 ≤ -em12497 := by
  apply negative_check (lo := (2740076550226466157 / 4000000000000000000)) (hi := (34250956877830826963 / 50000000000000000000))
    (y := (-((71704713971008292067 / 100000000000000000000)))) (u := (48819169154780119753 / 100000000000000000000))
  · norm_num [world12497, agent12497, scalar12497, tp12497, tm12497, ep12497, em12497, dsL]
  · norm_num [world12497, agent12497, scalar12497, tp12497, tm12497, ep12497, em12497, dsL]
  · norm_num [world12497, agent12497, scalar12497, tp12497, tm12497, ep12497, em12497, dsL]
  · norm_num [world12497, agent12497, scalar12497, tp12497, tm12497, ep12497, em12497, dsL]
  · norm_num [world12497, agent12497, scalar12497, tp12497, tm12497, ep12497, em12497, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12497, agent12497, tp12497, tm12497, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12497, agent12497, tp12497, tm12497, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12497, agent12497, scalar12497, tp12497, tm12497, ep12497, em12497, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12497, agent12497, tp12497, tm12497, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12497, agent12497, scalar12497, tp12497, tm12497, ep12497, em12497, dsL]

theorem tails12497 :
    exp (-((12497:ℝ)*ep12497)) ≤ scalar12497.upperTail ∧
    exp (-((12497:ℝ)*em12497)) ≤ scalar12497.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12497:ℝ)) (by norm_num [ep12497]) ?_)
      (show bp12497^8 ≤ scalar12497.upperTail by norm_num [bp12497, scalar12497])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12497, bp12497, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12497:ℝ)) (by norm_num [em12497]) ?_)
      (show bm12497^8 ≤ scalar12497.lowerTail by norm_num [bm12497, scalar12497])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12497, bm12497, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12497 :
    agent12497.root+dsL+scalar12497.worldRadius < √(1/100/aL) ∧
    2*(agent12497.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12497, agent12497, scalar12497, tp12497, tm12497, ep12497, em12497, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12497, agent12497, scalar12497, tp12497, tm12497, ep12497, em12497, dsL]

noncomputable def master12497 : MasterCertificate 12497 world12497 agent12497 :=
  master scalar12497 dsL tp12497 tm12497 ep12497 em12497
    (by norm_num [dsL]) (by norm_num [tp12497]) (by norm_num [tm12497])
    (by norm_num [ep12497]) (by norm_num [em12497])
    positive12497 negative12497 tails12497.1 tails12497.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12497.1 tailGuards12497.2

theorem preserves12497 : master12497.toScalarCertificate = scalar12497 := rfl

noncomputable def tp12498 : ℝ := (91880193 / 400000000)
noncomputable def tm12498 : ℝ := (-((6019585359 / 10000000000)))
noncomputable def ep12498 : ℝ := (1016829393701899 / 2000000000000000000)
noncomputable def em12498 : ℝ := (9920186712001833 / 20000000000000000000)
noncomputable def bp12498 : ℝ := (45191062086366375673 / 100000000000000000000)
noncomputable def bm12498 : ℝ := (23037709593616447331 / 50000000000000000000)

theorem positive12498 :
    Eplus aL (agent12498.root+dsL) scalar12498.worldRadius world12498.frame
      agent12498.frame tp12498 ≤ -ep12498 := by
  apply positive_check (eT := (57764978033201520319 / 50000000000000000000)) (y := (18854477685359484759 / 50000000000000000000)) (u := (36450871898828284943 / 25000000000000000000))
  · norm_num [world12498, agent12498, scalar12498, tp12498, tm12498, ep12498, em12498, dsL]
  · norm_num [world12498, agent12498, scalar12498, tp12498, tm12498, ep12498, em12498, dsL]
  · norm_num [world12498, agent12498, scalar12498, tp12498, tm12498, ep12498, em12498, dsL]
  · norm_num [world12498, agent12498, scalar12498, tp12498, tm12498, ep12498, em12498, dsL]
  · norm_num [world12498, agent12498, scalar12498, tp12498, tm12498, ep12498, em12498, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12498, agent12498, tp12498, tm12498, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12498, agent12498, scalar12498, tp12498, tm12498, ep12498, em12498, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12498, agent12498, tp12498, tm12498, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12498, agent12498, scalar12498, tp12498, tm12498, ep12498, em12498, dsL]

theorem negative12498 :
    Eminus aL (agent12498.root+dsL) scalar12498.worldRadius world12498.frame
      agent12498.frame tm12498 ≤ -em12498 := by
  apply negative_check (lo := (34250824162370637847 / 50000000000000000000)) (hi := (13700329664948255139 / 20000000000000000000))
    (y := (-((17926217380214719899 / 25000000000000000000)))) (u := (3051193326043406389 / 6250000000000000000))
  · norm_num [world12498, agent12498, scalar12498, tp12498, tm12498, ep12498, em12498, dsL]
  · norm_num [world12498, agent12498, scalar12498, tp12498, tm12498, ep12498, em12498, dsL]
  · norm_num [world12498, agent12498, scalar12498, tp12498, tm12498, ep12498, em12498, dsL]
  · norm_num [world12498, agent12498, scalar12498, tp12498, tm12498, ep12498, em12498, dsL]
  · norm_num [world12498, agent12498, scalar12498, tp12498, tm12498, ep12498, em12498, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12498, agent12498, tp12498, tm12498, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12498, agent12498, tp12498, tm12498, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12498, agent12498, scalar12498, tp12498, tm12498, ep12498, em12498, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12498, agent12498, tp12498, tm12498, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12498, agent12498, scalar12498, tp12498, tm12498, ep12498, em12498, dsL]

theorem tails12498 :
    exp (-((12498:ℝ)*ep12498)) ≤ scalar12498.upperTail ∧
    exp (-((12498:ℝ)*em12498)) ≤ scalar12498.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12498:ℝ)) (by norm_num [ep12498]) ?_)
      (show bp12498^8 ≤ scalar12498.upperTail by norm_num [bp12498, scalar12498])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12498, bp12498, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12498:ℝ)) (by norm_num [em12498]) ?_)
      (show bm12498^8 ≤ scalar12498.lowerTail by norm_num [bm12498, scalar12498])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12498, bm12498, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12498 :
    agent12498.root+dsL+scalar12498.worldRadius < √(1/100/aL) ∧
    2*(agent12498.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12498, agent12498, scalar12498, tp12498, tm12498, ep12498, em12498, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12498, agent12498, scalar12498, tp12498, tm12498, ep12498, em12498, dsL]

noncomputable def master12498 : MasterCertificate 12498 world12498 agent12498 :=
  master scalar12498 dsL tp12498 tm12498 ep12498 em12498
    (by norm_num [dsL]) (by norm_num [tp12498]) (by norm_num [tm12498])
    (by norm_num [ep12498]) (by norm_num [em12498])
    positive12498 negative12498 tails12498.1 tails12498.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12498.1 tailGuards12498.2

theorem preserves12498 : master12498.toScalarCertificate = scalar12498 := rfl

noncomputable def tp12499 : ℝ := (2297096743 / 10000000000)
noncomputable def tm12499 : ℝ := (-((3009891971 / 5000000000)))
noncomputable def ep12499 : ℝ := (12711079883412647 / 25000000000000000000)
noncomputable def em12499 : ℝ := (24801696236227231 / 50000000000000000000)
noncomputable def bp12499 : ℝ := (45186178228708983009 / 100000000000000000000)
noncomputable def bm12499 : ℝ := (9214158518086692489 / 20000000000000000000)

theorem positive12499 :
    Eplus aL (agent12499.root+dsL) scalar12499.worldRadius world12499.frame
      agent12499.frame tp12499 ≤ -ep12499 := by
  apply positive_check (eT := (115530243886493421399 / 100000000000000000000)) (y := (18854909831234737397 / 50000000000000000000)) (u := (72902373884137076337 / 50000000000000000000))
  · norm_num [world12499, agent12499, scalar12499, tp12499, tm12499, ep12499, em12499, dsL]
  · norm_num [world12499, agent12499, scalar12499, tp12499, tm12499, ep12499, em12499, dsL]
  · norm_num [world12499, agent12499, scalar12499, tp12499, tm12499, ep12499, em12499, dsL]
  · norm_num [world12499, agent12499, scalar12499, tp12499, tm12499, ep12499, em12499, dsL]
  · norm_num [world12499, agent12499, scalar12499, tp12499, tm12499, ep12499, em12499, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12499, agent12499, tp12499, tm12499, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12499, agent12499, scalar12499, tp12499, tm12499, ep12499, em12499, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12499, agent12499, tp12499, tm12499, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12499, agent12499, scalar12499, tp12499, tm12499, ep12499, em12499, dsL]

theorem negative12499 :
    Eminus aL (agent12499.root+dsL) scalar12499.worldRadius world12499.frame
      agent12499.frame tm12499 ≤ -em12499 := by
  apply negative_check (lo := (68501383194647878059 / 100000000000000000000)) (hi := (3425069159732393903 / 5000000000000000000))
    (y := (-((71705025056209362639 / 100000000000000000000)))) (u := (48819017285805814697 / 100000000000000000000))
  · norm_num [world12499, agent12499, scalar12499, tp12499, tm12499, ep12499, em12499, dsL]
  · norm_num [world12499, agent12499, scalar12499, tp12499, tm12499, ep12499, em12499, dsL]
  · norm_num [world12499, agent12499, scalar12499, tp12499, tm12499, ep12499, em12499, dsL]
  · norm_num [world12499, agent12499, scalar12499, tp12499, tm12499, ep12499, em12499, dsL]
  · norm_num [world12499, agent12499, scalar12499, tp12499, tm12499, ep12499, em12499, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12499, agent12499, tp12499, tm12499, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12499, agent12499, tp12499, tm12499, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12499, agent12499, scalar12499, tp12499, tm12499, ep12499, em12499, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12499, agent12499, tp12499, tm12499, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12499, agent12499, scalar12499, tp12499, tm12499, ep12499, em12499, dsL]

theorem tails12499 :
    exp (-((12499:ℝ)*ep12499)) ≤ scalar12499.upperTail ∧
    exp (-((12499:ℝ)*em12499)) ≤ scalar12499.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12499:ℝ)) (by norm_num [ep12499]) ?_)
      (show bp12499^8 ≤ scalar12499.upperTail by norm_num [bp12499, scalar12499])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12499, bp12499, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12499:ℝ)) (by norm_num [em12499]) ?_)
      (show bm12499^8 ≤ scalar12499.lowerTail by norm_num [bm12499, scalar12499])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12499, bm12499, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12499 :
    agent12499.root+dsL+scalar12499.worldRadius < √(1/100/aL) ∧
    2*(agent12499.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12499, agent12499, scalar12499, tp12499, tm12499, ep12499, em12499, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12499, agent12499, scalar12499, tp12499, tm12499, ep12499, em12499, dsL]

noncomputable def master12499 : MasterCertificate 12499 world12499 agent12499 :=
  master scalar12499 dsL tp12499 tm12499 ep12499 em12499
    (by norm_num [dsL]) (by norm_num [tp12499]) (by norm_num [tm12499])
    (by norm_num [ep12499]) (by norm_num [em12499])
    positive12499 negative12499 tails12499.1 tails12499.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12499.1 tailGuards12499.2

theorem preserves12499 : master12499.toScalarCertificate = scalar12499 := rfl

end BstLean.Part268
